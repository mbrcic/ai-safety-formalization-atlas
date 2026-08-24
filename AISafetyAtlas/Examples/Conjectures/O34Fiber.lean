module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Causal.Semialgebraic

/-!
# Adjudicating MAIS issue #4's complete `MAIS-O34(a)` criterion

`AISafetyAtlas.Conjectures.MAIS.maisO34_exactFiberCandidate` transcribes the
complete singleton criterion proposed by Rob Sneiderman in MAIS issue #4. This
module adjudicates it and holds nothing else.

The chart it is stated on, and the whole reading algebra the adjudication runs
on, sit in `AISafetyAtlas.Conjectures.BinaryPair`: which profile reads which
coordinate, when a coordinate is pinned, when it is invisible, and when two
orientations collide. That module is not library infrastructure — it is a fixed
two-variable chart shared with the MAIS-O31 statement, which is why it lives
beside the conjectures rather than in `AISafetyAtlas.Causal`. None of it is
specific to this question, so none of it lives here.

The criterion is adjudicated affirmatively. Sufficiency blocks every rival;
necessity splits into a same-direction half, which turns on a vanishing
direction difference hiding its coordinate from all sixteen profiles, and an
opposite-orientation half, which builds the mate that two flat lines allow.
`maisO34_exactFiberCandidate_holds` names the transcribed proposition.

The scope is the transcribed chart. Issue #4 part (b) is not covered.
-/

namespace AISafetyAtlas.Examples.Conjectures.O34

open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Conjectures.BinaryPair

/-! ## The same-orientation fibre -/

@[simp] public theorem other_zero : other 0 = 1 := rfl

@[simp] public theorem other_one : other 1 = 0 := rfl

/-- A valid model's own child coordinate always sits in the companion set of its
partner, so the criterion's singleton demand is a demand about that set only. -/
public theorem child_mem_separatedValues {M : PairModel} {lam : ℝ}
    (hM : M.Valid lam) (z : Fin 2) :
    M.child z ∈ separatedValues lam (M.child (other z)) := by
  obtain ⟨-, -, -, hch, hsep⟩ := hM
  refine ⟨hch z, ?_⟩
  fin_cases z
  · simpa [abs_sub_comm] using hsep
  · simpa using hsep

/-- **Same-orientation half of the criterion.** Under the candidate's
same-direction clause, no distinct model of the *same* orientation shares the
behaviour. -/
public theorem eq_of_sameGraph_of_candidate {M M' : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {lam : ℝ} (hlam : 0 < lam) (hg : ValidGap lam g)
    (_hM : M.Valid lam) (hM' : M'.Valid lam) (hgr : M'.orientation = M.orientation)
    (hb : BehaviorEq g M M')
    (hc : O34SameDirectionSingletonCandidate g lam M) :
    M' = M := by
  have hroot : M'.root = M.root := root_eq_of_behaviorEq_of_validGap hlam hg hgr hb
  have hchild : ∀ i, M'.child i = M.child i := by
    rcases hc with hall | ⟨z, hz, hoz, hset⟩
    · exact fun i ↦ child_eq_of_behaviorEq hgr hb (hall i)
    · have hother : M'.child (other z) = M.child (other z) :=
        child_eq_of_behaviorEq hgr hb hoz
      have hzeq : M'.child z = M.child z := by
        have hmem : M'.child z ∈ separatedValues lam (M.child (other z)) := by
          rw [← hother]; exact child_mem_separatedValues hM' z
        rw [hset] at hmem
        exact hmem
      intro i
      fin_cases i
      · fin_cases z
        · exact hzeq
        · exact hother
      · fin_cases z
        · exact hother
        · exact hzeq
  exact PairModel.ext hgr hroot (funext hchild)

/-- **Necessity of the mate conditions.** If some opposite-orientation model
shares the behaviour, the gap table must have exactly one flat row and exactly
one flat column, and the root's companion set must be inhabited — precisely the
three clauses of `O34HasOppositeDirectionMateCandidate`. -/
public theorem hasOppositeMate_of_opposite_mate {M M' : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {lam : ℝ} (hlam : 0 < lam) (hg : ValidGap lam g)
    (hM : M.Valid lam) (hM' : M'.Valid lam) (hgr : M'.orientation ≠ M.orientation)
    (hb : BehaviorEq g M M') :
    O34HasOppositeDirectionMateCandidate g lam M := by
  have hchildne : M.child 0 ≠ M.child 1 := by
    obtain ⟨-, -, -, -, hsep⟩ := hM
    intro h
    rw [h] at hsep
    simp at hsep
    linarith
  have hchildne' : M'.child 0 ≠ M'.child 1 := by
    obtain ⟨-, -, -, -, hsep⟩ := hM'
    intro h
    rw [h] at hsep
    simp at hsep
    linarith
  -- some direction difference vanishes, else both children collapse to `M'.root`
  have hzflat : ∃ z, childDifference M.orientation g z = 0 := by
    by_contra hcon
    push Not at hcon
    exact hchildne
      ((root_eq_child_of_opposite hgr hb (hcon 0)).symm.trans
        (root_eq_child_of_opposite hgr hb (hcon 1)))
  -- some opposite difference vanishes, else both of `M'`'s children collapse
  have hwflat : ∃ w, rootDifference M.orientation g w = 0 := by
    by_contra hcon
    push Not at hcon
    exact hchildne'
      ((child_eq_root_of_opposite hgr hb (hcon 0)).trans
        (child_eq_root_of_opposite hgr hb (hcon 1)).symm)
  obtain ⟨z, hz⟩ := hzflat
  obtain ⟨w, hw⟩ := hwflat
  obtain ⟨i, hi⟩ := exists_childDifference_ne_zero hM.1 hg M.orientation
  obtain ⟨v, hv⟩ := exists_rootDifference_ne_zero hlam hg M.orientation
  refine ⟨exactlyOneFlat_of hz hi, exactlyOneFlat_of hw hv, ?_⟩
  -- the free coordinate of `M'` witnesses that `M.root`'s companion set is inhabited
  have hvw : v = other w := eq_other_of_ne (fun h ↦ hv (by rw [h]; exact hw))
  have hpin : M'.child (other w) = M.root := by
    rw [← hvw]; exact child_eq_root_of_opposite hgr hb hv
  refine ⟨M'.child w, ?_⟩
  have hmem := child_mem_separatedValues hM' w
  rwa [hpin] at hmem

/-! ## Sufficiency of the submitted criterion -/

/-- **One direction of MAIS issue #4's candidate, proved.** If the submitted
criterion holds, the global behavioural fibre really is a singleton: no
same-orientation model survives the same-direction clause, and no
opposite-orientation model survives the mate clause.

The converse — that a singleton fibre forces the criterion — requires
exhibiting mates when the criterion fails; that direction is not this theorem,
it is `globalSingleton_of_isSingletonFiber` below, and the two combine into
`isSingletonFiber_iff_candidate`. -/
public theorem isSingletonFiber_of_candidate {M : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {lam : ℝ} (hg : ValidGap lam g)
    (hM : M.Valid lam) (hc : O34GlobalSingletonCandidate g lam M) :
    HasSingletonFibre g lam M := by
  obtain ⟨hsame, hopp⟩ := hc
  intro M' hM' hb
  by_cases hgr : M'.orientation = M.orientation
  · exact eq_of_sameGraph_of_candidate hM.1 hg hM hM' hgr hb hsame
  · exact absurd (hasOppositeMate_of_opposite_mate hM.1 hg hM hM' hgr hb) hopp

/-! ## Necessity of the same-direction clause

The first half of the converse. Sufficiency showed the criterion blocks every
rival; here the same-direction clause is shown to be *forced*: when it fails,
`child z` is both unread and free to move inside its companion set, so a mate
exists and the fibre is not a singleton.
-/

/-- **Branch 1 of the converse, proved.** If the submitted same-direction clause
fails, an explicit same-orientation mate exists. -/
public theorem exists_mate_of_not_sameDirection {M : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {lam : ℝ} (hg : ValidGap lam g)
    (hM : M.Valid lam) (hs : ¬ O34SameDirectionSingletonCandidate g lam M) :
    ∃ M' : PairModel, M'.Valid lam ∧ BehaviorEq g M M' ∧ M' ≠ M := by
  rw [O34SameDirectionSingletonCandidate, not_or] at hs
  obtain ⟨hnall, hnset⟩ := hs
  push Not at hnall
  obtain ⟨z, hz⟩ := hnall
  obtain ⟨i, hi⟩ := exists_childDifference_ne_zero hM.1 hg M.orientation
  have hiz : i = other z := eq_other_of_ne (fun h ↦ hi (by rw [h]; exact hz))
  have hoz : childDifference M.orientation g (other z) ≠ 0 := by rwa [hiz] at hi
  push Not at hnset
  have hne : separatedValues lam (M.child (other z)) ≠ {M.child z} :=
    hnset z hz hoz
  have hmem : M.child z ∈ separatedValues lam (M.child (other z)) :=
    child_mem_separatedValues hM z
  have hex : ∃ s ∈ separatedValues lam (M.child (other z)), s ≠ M.child z := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.eq_singleton_iff_unique_mem.mpr ⟨hmem, hcon⟩)
  obtain ⟨s, hsmem, hsne⟩ := hex
  obtain ⟨hlam', hhalf, hroot, hchild, -⟩ := hM
  refine ⟨⟨M.orientation, M.root, Function.update M.child z s⟩, ⟨hlam', hhalf, hroot, ?_, ?_⟩,
    ?_, ?_⟩
  · intro j
    by_cases hj : j = z
    · subst hj; simpa using hsmem.1
    · simpa [hj] using hchild j
  · fin_cases z <;>
      simpa [other, abs_sub_comm] using hsmem.2
  · refine behaviorEq_of_childDifference_eq_zero (M := M) rfl rfl ?_ hz
    simp
  · intro hcon
    apply hsne
    have h1 := congrArg (fun N : PairModel ↦ N.child z) hcon
    simpa using h1

/-- The same-direction clause is necessary for a singleton fibre. -/
public theorem sameDirection_of_isSingletonFiber {M : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {lam : ℝ} (hg : ValidGap lam g)
    (hM : M.Valid lam) (hfib : HasSingletonFibre g lam M) :
    O34SameDirectionSingletonCandidate g lam M := by
  by_contra hs
  obtain ⟨M', hM', hb, hneq⟩ := exists_mate_of_not_sameDirection hg hM hs
  exact hneq (hfib M' hM' hb)

/-! ## The clause can fail

`sameDirection_of_isSingletonFiber` would be empty if no valid gap and model
made the same-direction clause fail. One does. The flat row makes `child 0`
unread, and its partner's companion set is wider than the singleton the clause
demands, so the fibre of this model is not a singleton.
-/

/-- A valid gap whose first row is flat. -/
@[expose] public noncomputable def o34FlatRowGap : Fin 2 → Fin 2 → ℝ :=
  ![![1 / 2, 1 / 2], ![-(1 / 4), 3 / 4]]

/-- A valid forward model whose unread coordinate has room to move. -/
@[expose] public noncomputable def o34FlatRowModel : PairModel where
  orientation := Orientation.forward
  root := 1 / 2
  child := ![1 / 5, 4 / 5]

public theorem o34FlatRowGap_valid : ValidGap (1 / 10) o34FlatRowGap := by
  refine ⟨?_, ⟨0, 0, ?_⟩, ⟨1, 0, ?_⟩, ⟨0, ?_⟩, ⟨1, ?_⟩⟩
  · intro x y
    fin_cases x <;> fin_cases y <;> norm_num [o34FlatRowGap]
  · norm_num [o34FlatRowGap]
  · norm_num [o34FlatRowGap]
  · norm_num [o34FlatRowGap]
  · norm_num [o34FlatRowGap]

public theorem o34FlatRowModel_valid : o34FlatRowModel.Valid (1 / 10) := by
  refine ⟨by norm_num, by norm_num,
    ⟨by norm_num [o34FlatRowModel], by norm_num [o34FlatRowModel]⟩, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [InMarginInterval, o34FlatRowModel]
  · norm_num [o34FlatRowModel]

/-- **The same-direction clause is not vacuous.** -/
public theorem not_sameDirection_o34FlatRow :
    ¬ O34SameDirectionSingletonCandidate o34FlatRowGap (1 / 10) o34FlatRowModel := by
  have hd0 : childDifference o34FlatRowModel.orientation o34FlatRowGap 0 = 0 := by
    norm_num [childDifference, o34FlatRowModel, o34FlatRowGap]
  have hd1 : childDifference o34FlatRowModel.orientation o34FlatRowGap 1 = 1 := by
    norm_num [childDifference, o34FlatRowModel, o34FlatRowGap]
  rw [O34SameDirectionSingletonCandidate, not_or]
  refine ⟨?_, ?_⟩
  · push Not
    exact ⟨0, hd0⟩
  · push Not
    intro z hz _
    have hz0 : z = 0 := by
      rcases fin_two_eq_zero_or_one z with h | h
      · exact h
      · rw [h, hd1] at hz; norm_num at hz
    subst hz0
    intro hset
    have hmem : (3 / 10 : ℝ) ∈
        separatedValues (1 / 10) (o34FlatRowModel.child (other 0)) := by
      refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
      norm_num [o34FlatRowModel, other, abs_of_nonpos]
    rw [hset] at hmem
    have : (3 / 10 : ℝ) = o34FlatRowModel.child 0 := hmem
    norm_num [o34FlatRowModel] at this

/-- **Consequence.** This valid model's behavioural fibre is not a singleton, so
the same-direction clause of MAIS issue #4's criterion is genuinely necessary. -/
public theorem not_isSingletonFiber_o34FlatRow :
    ¬ HasSingletonFibre o34FlatRowGap (1 / 10) o34FlatRowModel := fun hfib ↦
  not_sameDirection_o34FlatRow
    (sameDirection_of_isSingletonFiber o34FlatRowGap_valid o34FlatRowModel_valid hfib)

/-! ## Necessity of the mate clause

`hasOppositeMate_of_opposite_mate` proved the three clauses are necessary for an
opposite-orientation mate. This proves they are sufficient, which is the step
the candidate needed and the only one that could have refuted it.
-/

/-- **Branch 2 of the converse, proved.** The three mate clauses build an
explicit opposite-orientation mate. -/
public theorem exists_oppositeMate_of_hasOppositeMate {M : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {lam : ℝ} (hM : M.Valid lam)
    (hc : O34HasOppositeDirectionMateCandidate g lam M) :
    ∃ M' : PairModel, M'.Valid lam ∧ BehaviorEq g M M' ∧ M' ≠ M := by
  obtain ⟨⟨z, hz, -⟩, ⟨w, hw, -⟩, s, hsm, hss⟩ := hc
  obtain ⟨hlam, hhalf, hrt, hchild, -⟩ := hM
  refine ⟨⟨otherOrientation M.orientation, M.child (other z),
      Function.update (fun _ ↦ s) (other w) M.root⟩,
    ⟨hlam, hhalf, hchild _, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    by_cases hj : j = other w
    · subst hj; simpa using hrt
    · simpa [hj] using hsm
  · have hne : w ≠ other w := (other_ne w).symm
    rcases fin_two_eq_zero_or_one w with hwv | hwv <;> subst hwv <;>
      simp only [other_zero, other_one] at hne ⊢ <;>
      simp only [Function.update_self, Function.update_of_ne hne] <;>
      simpa [abs_sub_comm] using hss
  · cases hgM : M.orientation with
    | forward =>
      rw [hgM] at hz hw
      refine behaviorEq_crossed_forward hgM (by simp [otherOrientation]) hz hw rfl ?_
      simp
    | reverse =>
      rw [hgM] at hz hw
      refine behaviorEq_crossed_reverse hgM (by simp [otherOrientation]) hz hw rfl ?_
      simp
  · intro hcon
    exact otherOrientation_ne M.orientation (congrArg PairModel.orientation hcon)

/-! ## The complete adjudication -/

/-- **Necessity of MAIS issue #4's criterion.** -/
public theorem globalSingleton_of_isSingletonFiber {M : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {lam : ℝ} (hg : ValidGap lam g) (hM : M.Valid lam)
    (hfib : HasSingletonFibre g lam M) :
    O34GlobalSingletonCandidate g lam M := by
  refine ⟨sameDirection_of_isSingletonFiber hg hM hfib, fun hc ↦ ?_⟩
  obtain ⟨M', hM', hb, hne⟩ := exists_oppositeMate_of_hasOppositeMate hM hc
  exact hne (hfib M' hM' hb)

/-- **MAIS issue #4's O34(a) criterion is exactly right.** -/
public theorem isSingletonFiber_iff_candidate {M : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {lam : ℝ} (hg : ValidGap lam g) (hM : M.Valid lam) :
    HasSingletonFibre g lam M ↔ O34GlobalSingletonCandidate g lam M :=
  ⟨globalSingleton_of_isSingletonFiber hg hM, isSingletonFiber_of_candidate hg hM⟩

/-- **CONJ-009 resolved affirmatively.** -/
public theorem maisO34_exactFiberCandidate_holds : maisO34_exactFiberCandidate :=
  fun _ _ _ hg hM ↦ isSingletonFiber_iff_candidate hg hM

/-- **The criterion decides the printed fibre, not merely the chart's.**

`isSingletonFiber_iff_candidate` compares `M` against other chart points.
`prob:starter-set`(a) asks when `{M' : 𝚫_{M'} = 𝚫_M}` is a singleton inside
`𝕄₂(λ)`, and identification claims get easier as the comparison class shrinks,
so the chart reading is print's only because `exists_pairModel_toModel_eq` shows
the chart reaches every model of the family. That surjectivity is what this
corollary spends: the left-hand side quantifies over every model of the printed
class carrying an edge. -/
public theorem o34_classFibre_iff_candidate {M : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {lam : ℝ} (hg : ValidGap lam g) (hM : M.Valid lam) :
    (∀ N : AISafetyAtlas.Causal.Model (Fin 2) (AISafetyAtlas.Causal.binaryDim (Fin 2)) ℝ,
        (pairSkeletonOfValid g hg).MarginClass N lam →
        (∃ c p, p ∈ N.parents c) →
        (pairSkeletonOfValid g hg).BehaviorEq
          (M.toModel (PairModel.inUnitBox_of_valid hM)) N →
        N = M.toModel (PairModel.inUnitBox_of_valid hM)) ↔
      O34GlobalSingletonCandidate g lam M :=
  (hasSingletonFibre_iff_kernel_class hg hM).symm.trans
    (isSingletonFiber_iff_candidate hg hM)

/-! ## Both sides of the equivalence are reachable

`isSingletonFiber_iff_candidate` would say nothing if either side were empty on
valid data. Neither is. One gap table has two flat lines, so the mate clause
holds and the fibre is not a singleton; another has no flat line at all, so the
criterion holds and the fibre is a singleton.
-/

/-- A valid gap with one flat row *and* one flat column. -/
@[expose] public noncomputable def o34TwoFlatGap : Fin 2 → Fin 2 → ℝ :=
  ![![1 / 2, 1 / 2], ![1 / 2, -(1 / 4)]]

@[expose] public noncomputable def o34TwoFlatModel : PairModel where
  orientation := Orientation.forward
  root := 1 / 2
  child := ![1 / 5, 4 / 5]

public theorem o34TwoFlatGap_valid : ValidGap (1 / 10) o34TwoFlatGap := by
  refine ⟨?_, ⟨0, 0, ?_⟩, ⟨1, 1, ?_⟩, ⟨1, ?_⟩, ⟨1, ?_⟩⟩
  · intro x y
    fin_cases x <;> fin_cases y <;> norm_num [o34TwoFlatGap]
  · norm_num [o34TwoFlatGap]
  · norm_num [o34TwoFlatGap]
  · norm_num [o34TwoFlatGap]
  · norm_num [o34TwoFlatGap]

public theorem o34TwoFlatModel_valid : o34TwoFlatModel.Valid (1 / 10) := by
  refine ⟨by norm_num, by norm_num,
    ⟨by norm_num [o34TwoFlatModel], by norm_num [o34TwoFlatModel]⟩, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [InMarginInterval, o34TwoFlatModel]
  · norm_num [o34TwoFlatModel]

/-- **The mate clause is reachable.** -/
public theorem hasOppositeMate_o34TwoFlat :
    O34HasOppositeDirectionMateCandidate o34TwoFlatGap (1 / 10) o34TwoFlatModel := by
  refine ⟨⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩, ⟨1 / 10, ⟨by norm_num, by norm_num⟩, ?_⟩⟩
  · norm_num [childDifference, o34TwoFlatModel, o34TwoFlatGap]
  · norm_num [childDifference, o34TwoFlatModel, o34TwoFlatGap]
  · norm_num [rootDifference, childDifference, o34TwoFlatModel, o34TwoFlatGap]
  · norm_num [rootDifference, childDifference, o34TwoFlatModel, o34TwoFlatGap]
  · norm_num [o34TwoFlatModel, abs_of_nonpos]

/-- **Consequence.** A valid model whose gap has two flat lines has a mate. -/
public theorem not_isSingletonFiber_o34TwoFlat :
    ¬ HasSingletonFibre o34TwoFlatGap (1 / 10) o34TwoFlatModel := by
  intro hfib
  obtain ⟨M', hM', hb, hne⟩ :=
    exists_oppositeMate_of_hasOppositeMate o34TwoFlatModel_valid hasOppositeMate_o34TwoFlat
  exact hne (hfib M' hM' hb)

/-- A valid gap with no flat line at all. -/
@[expose] public noncomputable def o34SharpGap : Fin 2 → Fin 2 → ℝ :=
  ![![1 / 2, -(1 / 4)], ![-(1 / 4), 1 / 2]]

public theorem o34SharpGap_valid : ValidGap (1 / 10) o34SharpGap := by
  refine ⟨?_, ⟨0, 0, ?_⟩, ⟨0, 1, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · intro x y
    fin_cases x <;> fin_cases y <;> norm_num [o34SharpGap]
  · norm_num [o34SharpGap]
  · norm_num [o34SharpGap]
  · norm_num [o34SharpGap]
  · norm_num [o34SharpGap]

/-- **The criterion is reachable.** -/
public theorem globalSingleton_o34Sharp :
    O34GlobalSingletonCandidate o34SharpGap (1 / 10) o34TwoFlatModel := by
  have hd : ∀ i : Fin 2,
      childDifference o34TwoFlatModel.orientation o34SharpGap i ≠ 0 := by
    intro i
    fin_cases i <;>
      norm_num [childDifference, o34TwoFlatModel, o34SharpGap]
  refine ⟨Or.inl hd, ?_⟩
  rintro ⟨⟨z, hz, -⟩, -, -⟩
  exact hd z hz

/-- **Consequence.** This valid model's fibre really is a singleton. -/
public theorem isSingletonFiber_o34Sharp :
    HasSingletonFibre o34SharpGap (1 / 10) o34TwoFlatModel :=
  isSingletonFiber_of_candidate o34SharpGap_valid o34TwoFlatModel_valid
    globalSingleton_o34Sharp


/-! ## The criterion is semialgebraic

`prob:starter-set`(a) asks for the singleton condition as *"an explicit
semialgebraic condition on `(u, θ)`"*. `o34_classFibre_iff_candidate` supplies
the condition and proves it decides the printed fibre; this section supplies the
missing adjective.

`def:twovar` names seven real coordinates — the four gap-table entries of `u`
and the three table parameters of `θ` — plus one binary structural choice, so
the locus lives in `ℝ⁷` once an orientation is fixed. Every atom of the
criterion is a polynomial sign condition in those coordinates: the child and
root differences are differences of gap entries, and the two clauses that
quantify over the reals are removed first by
`separatedValues_eq_singleton_iff` and `separatedValues_nonempty_iff`. What is
left is a boolean combination, and `IsSemialgebraic` is closed under those.
-/

/-- The seven real coordinates the printed condition is a condition on. -/
public abbrev O34Index := (Fin 2 × Fin 2) ⊕ Fin 3

/-- The gap table a chart point carries. -/
@[expose] public def o34ChartGap (q : O34Index → ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun x y ↦ q (Sum.inl (x, y))

/-- The model a chart point carries at a chosen orientation. -/
@[expose] public def o34ChartModel (gr : Orientation) (q : O34Index → ℝ) : PairModel where
  orientation := gr
  root := q (Sum.inr 0)
  child := fun i ↦ q (Sum.inr i.succ)

open MvPolynomial in
/-- The polynomial computing a child difference of the gap table. -/
@[expose] public noncomputable def o34ChildDiffPoly (gr : Orientation) (i : Fin 2) :
    MvPolynomial O34Index ℝ :=
  match gr with
  | .forward => X (Sum.inl (i, 1)) - X (Sum.inl (i, 0))
  | .reverse => X (Sum.inl (1, i)) - X (Sum.inl (0, i))

open MvPolynomial in
public theorem o34ChildDiffPoly_eval (gr : Orientation) (i : Fin 2) (q : O34Index → ℝ) :
    eval q (o34ChildDiffPoly gr i) = childDifference gr (o34ChartGap q) i := by
  cases gr <;> simp [o34ChildDiffPoly, childDifference, o34ChartGap]

open MvPolynomial in
public theorem o34RootDiffPoly_eval (gr : Orientation) (i : Fin 2) (q : O34Index → ℝ) :
    eval q (o34ChildDiffPoly (otherOrientation gr) i)
      = rootDifference gr (o34ChartGap q) i := by
  cases gr <;> simp [o34ChildDiffPoly, rootDifference, childDifference, o34ChartGap,
    otherOrientation]

open MvPolynomial in
/-- The polynomial reading one table coordinate, shifted by a constant. -/
@[expose] public noncomputable def o34ChildShiftPoly (i : Fin 2) (a : ℝ) :
    MvPolynomial O34Index ℝ :=
  X (Sum.inr i.succ) - C a

open MvPolynomial in
public theorem o34ChildShiftPoly_eval (i : Fin 2) (a : ℝ) (gr : Orientation)
    (q : O34Index → ℝ) :
    eval q (o34ChildShiftPoly i a) = (o34ChartModel gr q).child i - a := by
  simp [o34ChildShiftPoly, o34ChartModel]

open MvPolynomial in
/-- The polynomial reading the root coordinate, shifted by a constant. -/
@[expose] public noncomputable def o34RootShiftPoly (a : ℝ) : MvPolynomial O34Index ℝ :=
  X (Sum.inr 0) - C a

open MvPolynomial in
public theorem o34RootShiftPoly_eval (a : ℝ) (gr : Orientation) (q : O34Index → ℝ) :
    eval q (o34RootShiftPoly a) = (o34ChartModel gr q).root - a := by
  simp [o34RootShiftPoly, o34ChartModel]

open AISafetyAtlas.Causal MvPolynomial in
/-- A child coordinate meeting a constant is a semialgebraic condition. -/
private theorem isSemialgebraic_child_eq (gr : Orientation) (i : Fin 2) (a : ℝ) :
    IsSemialgebraic {q : O34Index → ℝ | (o34ChartModel gr q).child i = a} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ eval q (o34ChildShiftPoly i a) = 0) (fun q ↦ ?_)
    (isSemialgebraic_setOf_eval_eq_zero _)
  rw [o34ChildShiftPoly_eval i a gr q, sub_eq_zero]

open AISafetyAtlas.Causal MvPolynomial in
/-- A child difference vanishing is a semialgebraic condition. -/
private theorem isSemialgebraic_childDifference_eq_zero (gr : Orientation) (i : Fin 2) :
    IsSemialgebraic {q : O34Index → ℝ | childDifference gr (o34ChartGap q) i = 0} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ eval q (o34ChildDiffPoly gr i) = 0) (fun q ↦ ?_)
    (isSemialgebraic_setOf_eval_eq_zero _)
  rw [o34ChildDiffPoly_eval]

open AISafetyAtlas.Causal MvPolynomial in
private theorem isSemialgebraic_childDifference_ne_zero (gr : Orientation) (i : Fin 2) :
    IsSemialgebraic {q : O34Index → ℝ | childDifference gr (o34ChartGap q) i ≠ 0} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ eval q (o34ChildDiffPoly gr i) ≠ 0) (fun q ↦ ?_)
    (isSemialgebraic_setOf_eval_ne_zero _)
  rw [o34ChildDiffPoly_eval]

open AISafetyAtlas.Causal MvPolynomial in
private theorem isSemialgebraic_rootDifference_eq_zero (gr : Orientation) (i : Fin 2) :
    IsSemialgebraic {q : O34Index → ℝ | rootDifference gr (o34ChartGap q) i = 0} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ eval q (o34ChildDiffPoly (otherOrientation gr) i) = 0) (fun q ↦ ?_)
    (isSemialgebraic_setOf_eval_eq_zero _)
  rw [o34RootDiffPoly_eval]

open AISafetyAtlas.Causal MvPolynomial in
private theorem isSemialgebraic_rootDifference_ne_zero (gr : Orientation) (i : Fin 2) :
    IsSemialgebraic {q : O34Index → ℝ | rootDifference gr (o34ChartGap q) i ≠ 0} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ eval q (o34ChildDiffPoly (otherOrientation gr) i) ≠ 0) (fun q ↦ ?_)
    (isSemialgebraic_setOf_eval_ne_zero _)
  rw [o34RootDiffPoly_eval]

open AISafetyAtlas.Causal MvPolynomial in
/-- `ExactlyOneFlat` is a finite disjunction over `Fin 2`, hence semialgebraic
whenever its two atoms are. -/
private theorem isSemialgebraic_exactlyOneFlat
    {d : (O34Index → ℝ) → Fin 2 → ℝ}
    (hz : ∀ i, IsSemialgebraic {q : O34Index → ℝ | d q i = 0})
    (hn : ∀ i, IsSemialgebraic {q : O34Index → ℝ | d q i ≠ 0}) :
    IsSemialgebraic {q : O34Index → ℝ | ExactlyOneFlat (d q)} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ (d q 0 = 0 ∧ d q 1 ≠ 0) ∨ (d q 1 = 0 ∧ d q 0 ≠ 0))
    (fun q ↦ ?_) ?_
  · simp [ExactlyOneFlat, Fin.exists_fin_two]
  · exact ((hz 0).setOf_and (hn 1)).setOf_or ((hz 1).setOf_and (hn 0))

open AISafetyAtlas.Causal MvPolynomial in
/-- The companion clause, after its real quantifier is eliminated. -/
private theorem isSemialgebraic_companion_singleton {lam : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2) (gr : Orientation) (z : Fin 2) :
    IsSemialgebraic {q : O34Index → ℝ |
      separatedValues lam ((o34ChartModel gr q).child (other z))
        = {(o34ChartModel gr q).child z}} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ 1 < 4 * lam ∧
      (((o34ChartModel gr q).child (other z) = 2 * lam ∧
          (o34ChartModel gr q).child z = lam) ∨
        ((o34ChartModel gr q).child (other z) = 1 - 2 * lam ∧
          (o34ChartModel gr q).child z = 1 - lam)))
    (fun q ↦ separatedValues_eq_singleton_iff hlam0 hlam2) ?_
  exact IsSemialgebraic.setOf_const_and
    (((isSemialgebraic_child_eq gr (other z) (2 * lam)).setOf_and
        (isSemialgebraic_child_eq gr z lam)).setOf_or
      ((isSemialgebraic_child_eq gr (other z) (1 - 2 * lam)).setOf_and
        (isSemialgebraic_child_eq gr z (1 - lam))))

open AISafetyAtlas.Causal MvPolynomial in
/-- The mate clause's nonemptiness condition, after its real quantifier is
eliminated: two half-planes in the root coordinate. -/
private theorem isSemialgebraic_companion_nonempty {lam : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2) (gr : Orientation) :
    IsSemialgebraic {q : O34Index → ℝ |
      (separatedValues lam (o34ChartModel gr q).root).Nonempty} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ 2 * lam ≤ (o34ChartModel gr q).root ∨
      (o34ChartModel gr q).root ≤ 1 - 2 * lam)
    (fun q ↦ separatedValues_nonempty_iff hlam0 hlam2) ?_
  refine IsSemialgebraic.setOf_or ?_ ?_
  · refine IsSemialgebraic.setOf_congr
      (Q := fun q ↦ 0 ≤ eval q (o34RootShiftPoly (2 * lam))) (fun q ↦ ?_)
      (isSemialgebraic_setOf_eval_nonneg _)
    rw [o34RootShiftPoly_eval _ gr q, sub_nonneg]
  · refine IsSemialgebraic.setOf_congr
      (Q := fun q ↦ 0 ≤ eval q (-o34RootShiftPoly (1 - 2 * lam))) (fun q ↦ ?_)
      (isSemialgebraic_setOf_eval_nonneg _)
    rw [map_neg, o34RootShiftPoly_eval _ gr q, neg_sub, sub_nonneg]

open AISafetyAtlas.Causal MvPolynomial in
/-- **The criterion is semialgebraic**, which is the adjective
`prob:starter-set`(a) uses and the last unproved word of its part (a).

Fixing an orientation fixes the structural choice `def:twovar` offers; the
condition on the remaining seven real coordinates is a boolean combination of
polynomial sign conditions. -/
public theorem isSemialgebraic_o34GlobalSingletonCandidate {lam : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2) (gr : Orientation) :
    IsSemialgebraic {q : O34Index → ℝ |
      O34GlobalSingletonCandidate (o34ChartGap q) lam (o34ChartModel gr q)} := by
  have hgr : ∀ q : O34Index → ℝ, (o34ChartModel gr q).orientation = gr := fun _ ↦ rfl
  have hsame : IsSemialgebraic {q : O34Index → ℝ |
      O34SameDirectionSingletonCandidate (o34ChartGap q) lam (o34ChartModel gr q)} := by
    refine IsSemialgebraic.setOf_congr
      (Q := fun q ↦
        (childDifference gr (o34ChartGap q) 0 ≠ 0 ∧
          childDifference gr (o34ChartGap q) 1 ≠ 0) ∨
        ((childDifference gr (o34ChartGap q) 0 = 0 ∧
            childDifference gr (o34ChartGap q) 1 ≠ 0 ∧
            separatedValues lam ((o34ChartModel gr q).child (other 0))
              = {(o34ChartModel gr q).child 0}) ∨
          (childDifference gr (o34ChartGap q) 1 = 0 ∧
            childDifference gr (o34ChartGap q) 0 ≠ 0 ∧
            separatedValues lam ((o34ChartModel gr q).child (other 1))
              = {(o34ChartModel gr q).child 1})))
      (fun q ↦ ?_) ?_
    · simp only [O34SameDirectionSingletonCandidate, hgr, Fin.forall_fin_two,
        Fin.exists_fin_two, other_zero, other_one]
    · refine IsSemialgebraic.setOf_or
        ((isSemialgebraic_childDifference_ne_zero gr 0).setOf_and
          (isSemialgebraic_childDifference_ne_zero gr 1)) ?_
      refine IsSemialgebraic.setOf_or ?_ ?_
      · exact (isSemialgebraic_childDifference_eq_zero gr 0).setOf_and
          ((isSemialgebraic_childDifference_ne_zero gr 1).setOf_and
            (isSemialgebraic_companion_singleton hlam0 hlam2 gr 0))
      · exact (isSemialgebraic_childDifference_eq_zero gr 1).setOf_and
          ((isSemialgebraic_childDifference_ne_zero gr 0).setOf_and
            (isSemialgebraic_companion_singleton hlam0 hlam2 gr 1))
  have hmate : IsSemialgebraic {q : O34Index → ℝ |
      O34HasOppositeDirectionMateCandidate (o34ChartGap q) lam (o34ChartModel gr q)} := by
    refine IsSemialgebraic.setOf_congr
      (Q := fun q ↦ ExactlyOneFlat (childDifference gr (o34ChartGap q)) ∧
        ExactlyOneFlat (rootDifference gr (o34ChartGap q)) ∧
        (separatedValues lam (o34ChartModel gr q).root).Nonempty)
      (fun q ↦ by simp only [O34HasOppositeDirectionMateCandidate, hgr]) ?_
    refine IsSemialgebraic.setOf_and
      (isSemialgebraic_exactlyOneFlat (isSemialgebraic_childDifference_eq_zero gr)
        (isSemialgebraic_childDifference_ne_zero gr)) ?_
    exact IsSemialgebraic.setOf_and
      (isSemialgebraic_exactlyOneFlat (isSemialgebraic_rootDifference_eq_zero gr)
        (isSemialgebraic_rootDifference_ne_zero gr))
      (isSemialgebraic_companion_nonempty hlam0 hlam2 gr)
  exact hsame.setOf_and hmate.setOf_not

/-! ## The criterion, reached from a model of the printed class

`o34_classFibre_iff_candidate` compares a chart point's fibre against every model
of `𝕄₂(λ)`, which fixes the *rivals*. Its own subject is still a `PairModel`, and
so is `maisO34_exactFiberCandidate`'s outer binder — so on their face both speak
about chart points, and a universal over a smaller class asserts less.

`exists_pairModel_toModel_eq` says the two ranges coincide. This is the theorem
that spends it: start from a model of the printed class carrying an edge, and the
criterion is available for *that* model, at the chart point its own tables name.
Without it the surjectivity lemma has a consumer for the inner quantifier and
none for the outer one; `o31Classification_of_candidate` is the same theorem for
MAIS-O31. -/

/-- **Every printed model with an edge has the criterion.** `def:twovar`'s family
is exactly the models carrying one of the two arrows, so this is
`prob:starter-set`(a)'s subject rather than a chart-indexed proxy for it. -/
public theorem exists_pairModel_classFibre_iff_candidate {g : Fin 2 → Fin 2 → ℝ}
    {lam : ℝ} (hg : ValidGap lam g)
    {N : AISafetyAtlas.Causal.Model (Fin 2) (AISafetyAtlas.Causal.binaryDim (Fin 2)) ℝ}
    (hN : (pairSkeletonOfValid g hg).MarginClass N lam)
    (hedge : ∃ c p, p ∈ N.parents c) :
    ∃ P : PairModel, ∃ hP : P.Valid lam,
      P.toModel (PairModel.inUnitBox_of_valid hP) = N ∧
      ((∀ N' : AISafetyAtlas.Causal.Model (Fin 2) (AISafetyAtlas.Causal.binaryDim (Fin 2)) ℝ,
          (pairSkeletonOfValid g hg).MarginClass N' lam →
          (∃ c p, p ∈ N'.parents c) →
          (pairSkeletonOfValid g hg).BehaviorEq N N' → N' = N)
        ↔ O34GlobalSingletonCandidate g lam P) := by
  obtain ⟨P, hP, rfl⟩ := exists_pairModel_toModel_eq hg hN hedge
  exact ⟨P, hP, rfl, o34_classFibre_iff_candidate hg hP⟩


end AISafetyAtlas.Examples.Conjectures.O34
