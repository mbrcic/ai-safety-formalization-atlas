module

public import AISafetyAtlas.Causal.MarginClass
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

/-!
# The real three-coordinate chart for two binary variables

**This is a fixed chart, not an unrestricted causal-model type.** It has exactly
two binary variables, exactly one edge, and three real coordinates. Every valid
chart point embeds in `AISafetyAtlas.Causal.Model`, and the bridge below proves
the chart and kernel calculations agree. The chart remains useful because its
quantifiers range over exactly the three-coordinate family MAIS names.

The atlas has already recorded why it cannot be replaced by an unrestricted
kernel quantifier. This chart, under its old name, and the O31 chain are not the
kernel at a different field: parametrizing the kernel over its value field did
not absorb the chart coordinates.
That parametrization did retire one of the three original reasons -- mixtures
are field-generic on both sides now -- and the two that remain are what
matter. Minimal coordinates: `PairModel` is `@[ext]` on three numbers,
whereas `Model.ext` needs equality of a function-valued table together with
`parents`, so quantifying over `Model` ranges past the chart image and would
adjudicate a different question than the one the source asks in chart
coordinates. And sign agreement, in the O31 chain, is a decision-layer notion
rather than transform equality.

A third reason used to be listed and is now retired. The note said the
arithmetic here "merely has the same *shape* as the kernel's" and that nothing
proved `interventionFactor` agrees with `Model.factor`. Since 2026-08-21
something does: `PairModel.toModel` builds the kernel model a chart point in the
unit box names, `PairModel.factor_toModel` proves its `Model.factor` **is**
`interventionFactor`, and `PairModel.jointProb_toModel` and `PairModel.Δ_toModel`
carry that up to the interventional joint and the behavioural transform. The two
reasons above are unaffected — the chart stays. What is gone is the possibility
that the two arithmetics silently disagree, which was never a scope question and
always a correctness one.

What it does carry is shared between its two consumers, which is the only claim
made for it: `InMarginInterval` is used by the O31 chain as well, and the
agenda names the same chart as what MAIS-O35 would need.

Names describe the object rather than the question. `childDifference` is the
difference a profile reads a *child* coordinate through; `rootDifference` the
one it reads the *root* through. The agenda's row/column framing is
orientation-relative — a "row" difference reads a column in the reverse chart —
so it is kept only in docstrings and in the criterion propositions a reviewer
checks against MAIS issue #4.
-/

namespace AISafetyAtlas.Conjectures.BinaryPair

/-- The two possible one-edge orientations in the source's family `M₂(λ)`. -/
public inductive Orientation where
  | forward
  | reverse
  deriving DecidableEq

/-- The source's three-coordinate real chart for one orientation of `M₂(λ)`.

For `forward`, `root = P(X=1)` and `child x = P(Y=1 | X=x)`.
For `reverse`, `root = P(Y=1)` and `child y = P(X=1 | Y=y)`. -/
@[ext] public structure PairModel where
  orientation : Orientation
  root : ℝ
  child : Fin 2 → ℝ

/-- A real number lies in the source's closed probability margin interval. -/
@[expose] public def InMarginInterval (lam x : ℝ) : Prop :=
  lam ≤ x ∧ x ≤ 1 - lam

/-- Membership in the real two-variable one-edge model family. -/
@[expose] public def PairModel.Valid (lam : ℝ) (M : PairModel) : Prop :=
  0 < lam ∧ lam < 1 / 2 ∧
    InMarginInterval lam M.root ∧
    (∀ i, InMarginInterval lam (M.child i)) ∧
    lam ≤ |M.child 1 - M.child 0|

/-- The utility-gap conditions printed for the two-variable family. -/
@[expose] public def ValidGap (lam : ℝ) (g : Fin 2 → Fin 2 → ℝ) : Prop :=
  (∀ x y, lam ≤ |g x y| ∧ |g x y| ≤ 1) ∧
    (∃ x y, 0 < g x y) ∧ (∃ x y, g x y < 0) ∧
    (∃ y, lam ≤ |g 1 y - g 0 y|) ∧
    (∃ x, lam ≤ |g x 1 - g x 0|)

/-- The Bernoulli mass with success probability `p`. -/
@[expose] public noncomputable def bernoulli (p : ℝ) (a : Fin 2) : ℝ :=
  if a = 1 then p else 1 - p

/-- One transformed Bernoulli factor, the two-state instance of RE24 equation (1). -/
@[expose] public noncomputable def interventionFactor (p : ℝ) (f : Fin 2 → Fin 2)
    (realized : Fin 2) : ℝ :=
  ∑ a : Fin 2, if f a = realized then bernoulli p a else 0

/-- A local intervention on each of the two chance variables. -/
public abbrev Profile := (Fin 2) → (Fin 2 → Fin 2)

/-- The real interventional joint associated with the source's parameter chart. -/
@[expose] public noncomputable def PairModel.jointProb (M : PairModel)
    (profile : Profile) (x y : Fin 2) : ℝ :=
  match M.orientation with
  | .forward => interventionFactor M.root (profile 0) x * interventionFactor (M.child x) (profile 1) y
  | .reverse => interventionFactor M.root (profile 1) y * interventionFactor (M.child y) (profile 0) x

/-- One of the sixteen real behavioral-transform coordinates. -/
@[expose] public noncomputable def PairModel.transform (M : PairModel)
    (g : Fin 2 → Fin 2 → ℝ) (profile : Profile) : ℝ :=
  ∑ x : Fin 2, ∑ y : Fin 2, M.jointProb profile x y * g x y

/-- Equality of all sixteen coordinates of the real two-variable transform. -/
@[expose] public noncomputable def BehaviorEq (g : Fin 2 → Fin 2 → ℝ)
    (M M' : PairModel) : Prop :=
  ∀ profile : Profile, M.transform g profile = M'.transform g profile

/-- The global behavioral fibre of `M` inside the margin class is a singleton. -/
@[expose] public noncomputable def HasSingletonFibre (g : Fin 2 → Fin 2 → ℝ)
    (lam : ℝ) (M : PairModel) : Prop :=
  ∀ M' : PairModel, M'.Valid lam → BehaviorEq g M M' → M' = M

/-- The other value of a binary index. -/
@[expose] public def other (i : Fin 2) : Fin 2 :=
  if i = 0 then 1 else 0

/-- Row differences in the forward chart and column differences in the reverse chart. -/
@[expose] public def childDifference (orientation : Orientation)
    (g : Fin 2 → Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  match orientation with
  | .forward => g i 1 - g i 0
  | .reverse => g 1 i - g 0 i

/-- The differences used by the opposite orientation. -/
@[expose] public def rootDifference (orientation : Orientation)
    (g : Fin 2 → Fin 2 → ℝ) : Fin 2 → ℝ :=
  match orientation with
  | .forward => childDifference .reverse g
  | .reverse => childDifference .forward g

/-- Exactly one row or column of the gap table is flat. -/
@[expose] public def ExactlyOneFlat (difference : Fin 2 → ℝ) : Prop :=
  ∃ z, difference z = 0 ∧ difference (other z) ≠ 0

/-- Feasible companion parameters separated from `t` by the edge margin. -/
@[expose] public def separatedValues (lam t : ℝ) : Set ℝ :=
  {s | InMarginInterval lam s ∧ lam ≤ |s - t|}

/-! ## The four local interventions on a binary variable -/

/-- The constant local intervention, the source's hard intervention. -/
@[expose] public def cst (b : Fin 2) : Fin 2 → Fin 2 := fun _ ↦ b

@[simp] public theorem bernoulli_sum (p : ℝ) :
    ∑ a : Fin 2, bernoulli p a = 1 := by
  simp [bernoulli, Fin.sum_univ_two]

@[simp] public theorem factor_cst (p : ℝ) (b r : Fin 2) :
    interventionFactor p (cst b) r = if b = r then 1 else 0 := by
  unfold interventionFactor cst
  by_cases h : b = r <;> simp [h, bernoulli, Fin.sum_univ_two]

@[simp] public theorem factor_id (p : ℝ) (r : Fin 2) :
    interventionFactor p id r = bernoulli p r := by
  unfold interventionFactor
  -- `simp` alone now closes this; the sum lemma and the case split are no
  -- longer reached.
  simp

/-- A profile from its two local interventions. -/
@[expose] public def prof (fX fY : Fin 2 → Fin 2) : Profile := ![fX, fY]

@[simp] public theorem prof_zero (fX fY : Fin 2 → Fin 2) : prof fX fY 0 = fX := rfl

@[simp] public theorem prof_one (fX fY : Fin 2 → Fin 2) : prof fX fY 1 = fY := rfl

/-! ## The two reading profiles -/

/-- Forcing the first variable to `b` and observing the second. In the forward
chart this reads `child b`; in the reverse chart the first variable is the
child, so the same profile reads `root`. -/
public theorem transform_force_fst (M : PairModel) (g : Fin 2 → Fin 2 → ℝ)
    (b : Fin 2) :
    M.transform g (prof (cst b) id) =
      if M.orientation = .forward then
        g b 0 + M.child b * (g b 1 - g b 0)
      else g b 0 + M.root * (g b 1 - g b 0) := by
  unfold PairModel.transform PairModel.jointProb
  cases hg : M.orientation <;>
    simp [Fin.sum_univ_two, bernoulli] <;>
    fin_cases b <;> simp <;> ring

/-- Observing the first variable and forcing the second to `w`. In the forward
chart this reads `root`; in the reverse chart it reads `child w`. -/
public theorem transform_force_snd (M : PairModel) (g : Fin 2 → Fin 2 → ℝ)
    (w : Fin 2) :
    M.transform g (prof id (cst w)) =
      if M.orientation = .forward then
        g 0 w + M.root * (g 1 w - g 0 w)
      else g 0 w + M.child w * (g 1 w - g 0 w) := by
  unfold PairModel.transform PairModel.jointProb
  cases hg : M.orientation <;>
    simp [Fin.sum_univ_two, bernoulli] <;>
    fin_cases w <;> simp <;> ring

/-! ## Identification

Both readings are uniform in the orientation once stated through the source's
own difference vectors: `childDifference` is the difference that reads a
child coordinate, and `rootDifference` is the one that reads the root.
-/

/-- A nonzero direction difference pins that child coordinate against any
same-orientation model with the same behaviour. -/
public theorem child_eq_of_behaviorEq {M M' : PairModel} {g : Fin 2 → Fin 2 → ℝ}
    {i : Fin 2} (hgr : M'.orientation = M.orientation) (hb : BehaviorEq g M M')
    (hd : childDifference M.orientation g i ≠ 0) :
    M'.child i = M.child i := by
  cases hgM : M.orientation
  · have h1 := transform_force_fst M g i
    have h2 := transform_force_fst M' g i
    rw [hgM] at h1
    rw [hgr, hgM] at h2
    norm_num at h1 h2
    have hEq := hb (prof (cst i) id)
    rw [h1, h2] at hEq
    have hD : g i 1 - g i 0 ≠ 0 := by
      simpa [childDifference, hgM] using hd
    have : M.child i * (g i 1 - g i 0) = M'.child i * (g i 1 - g i 0) := by linarith
    exact (mul_right_cancel₀ hD this).symm
  · have h1 := transform_force_snd M g i
    have h2 := transform_force_snd M' g i
    rw [hgM] at h1
    rw [hgr, hgM] at h2
    simp at h1 h2
    have hEq := hb (prof id (cst i))
    rw [h1, h2] at hEq
    have hD : g 1 i - g 0 i ≠ 0 := by
      simpa [childDifference, hgM] using hd
    have : M.child i * (g 1 i - g 0 i) = M'.child i * (g 1 i - g 0 i) := by linarith
    exact (mul_right_cancel₀ hD this).symm

/-- A nonzero opposite difference pins the root against any same-orientation
model with the same behaviour. -/
public theorem root_eq_of_behaviorEq {M M' : PairModel} {g : Fin 2 → Fin 2 → ℝ}
    {w : Fin 2} (hgr : M'.orientation = M.orientation) (hb : BehaviorEq g M M')
    (he : rootDifference M.orientation g w ≠ 0) :
    M'.root = M.root := by
  cases hgM : M.orientation
  · have h1 := transform_force_snd M g w
    have h2 := transform_force_snd M' g w
    rw [hgM] at h1
    rw [hgr, hgM] at h2
    norm_num at h1 h2
    have hEq := hb (prof id (cst w))
    rw [h1, h2] at hEq
    have hD : g 1 w - g 0 w ≠ 0 := by
      simpa [rootDifference, childDifference, hgM] using he
    have : M.root * (g 1 w - g 0 w) = M'.root * (g 1 w - g 0 w) := by linarith
    exact (mul_right_cancel₀ hD this).symm
  · have h1 := transform_force_fst M g w
    have h2 := transform_force_fst M' g w
    rw [hgM] at h1
    rw [hgr, hgM] at h2
    simp at h1 h2
    have hEq := hb (prof (cst w) id)
    rw [h1, h2] at hEq
    have hD : g w 1 - g w 0 ≠ 0 := by
      simpa [rootDifference, childDifference, hgM] using he
    have : M.root * (g w 1 - g w 0) = M'.root * (g w 1 - g w 0) := by linarith
    exact (mul_right_cancel₀ hD this).symm

/-- `ValidGap` always supplies a nonzero opposite difference, so the root is
pinned unconditionally. This is why the criterion never mentions the root's
identifiability: it is automatic. -/
public theorem exists_rootDifference_ne_zero {lam : ℝ} {g : Fin 2 → Fin 2 → ℝ}
    (hlam : 0 < lam) (hg : ValidGap lam g) (orientation : Orientation) :
    ∃ w, rootDifference orientation g w ≠ 0 := by
  obtain ⟨-, -, -, ⟨y, hy⟩, ⟨x, hx⟩⟩ := hg
  cases orientation
  · exact ⟨y, by
      simp only [rootDifference, childDifference]
      intro h
      rw [h] at hy
      simp at hy
      linarith⟩
  · exact ⟨x, by
      simp only [rootDifference, childDifference]
      intro h
      rw [h] at hx
      simp at hx
      linarith⟩

/-- The root is pinned outright, for any valid gap. -/
public theorem root_eq_of_behaviorEq_of_validGap {M M' : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {lam : ℝ} (hlam : 0 < lam) (hg : ValidGap lam g)
    (hgr : M'.orientation = M.orientation) (hb : BehaviorEq g M M') :
    M'.root = M.root := by
  obtain ⟨w, hw⟩ := exists_rootDifference_ne_zero hlam hg M.orientation
  exact root_eq_of_behaviorEq hgr hb hw

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


/-! ## The opposite-orientation fibre

Swapping the orientation swaps which coordinate each profile reads. The profile
that reads `M.child i` reads `M'.root`, against the same multiplier; the profile
that reads `M.root` reads `M'.child w`. That crossing is what forces the flat
row and flat column the criterion demands. -/

/-- With opposite orientations, a nonzero direction difference identifies
`M'.root` with `M.child i`. -/
public theorem root_eq_child_of_opposite {M M' : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {i : Fin 2} (hgr : M'.orientation ≠ M.orientation)
    (hb : BehaviorEq g M M') (hd : childDifference M.orientation g i ≠ 0) :
    M'.root = M.child i := by
  cases hgM : M.orientation <;> cases hgM' : M'.orientation <;>
    rw [hgM] at hgr <;> rw [hgM'] at hgr <;> simp at hgr
  · have h1 := transform_force_fst M g i
    have h2 := transform_force_fst M' g i
    rw [hgM] at h1
    rw [hgM'] at h2
    simp at h1 h2
    have hEq := hb (prof (cst i) id)
    rw [h1, h2] at hEq
    have hD : g i 1 - g i 0 ≠ 0 := by
      simpa [childDifference, hgM] using hd
    have : M'.root * (g i 1 - g i 0) = M.child i * (g i 1 - g i 0) := by linarith
    exact mul_right_cancel₀ hD this
  · have h1 := transform_force_snd M g i
    have h2 := transform_force_snd M' g i
    rw [hgM] at h1
    rw [hgM'] at h2
    simp at h1 h2
    have hEq := hb (prof id (cst i))
    rw [h1, h2] at hEq
    have hD : g 1 i - g 0 i ≠ 0 := by
      simpa [childDifference, hgM] using hd
    have : M'.root * (g 1 i - g 0 i) = M.child i * (g 1 i - g 0 i) := by linarith
    exact mul_right_cancel₀ hD this

/-- With opposite orientations, a nonzero opposite difference identifies
`M'.child w` with `M.root`. -/
public theorem child_eq_root_of_opposite {M M' : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {w : Fin 2} (hgr : M'.orientation ≠ M.orientation)
    (hb : BehaviorEq g M M') (he : rootDifference M.orientation g w ≠ 0) :
    M'.child w = M.root := by
  cases hgM : M.orientation <;> cases hgM' : M'.orientation <;>
    rw [hgM] at hgr <;> rw [hgM'] at hgr <;> simp at hgr
  · have h1 := transform_force_snd M g w
    have h2 := transform_force_snd M' g w
    rw [hgM] at h1
    rw [hgM'] at h2
    simp at h1 h2
    have hEq := hb (prof id (cst w))
    rw [h1, h2] at hEq
    have hD : g 1 w - g 0 w ≠ 0 := by
      simpa [rootDifference, childDifference, hgM] using he
    have : M'.child w * (g 1 w - g 0 w) = M.root * (g 1 w - g 0 w) := by linarith
    exact mul_right_cancel₀ hD this
  · have h1 := transform_force_fst M g w
    have h2 := transform_force_fst M' g w
    rw [hgM] at h1
    rw [hgM'] at h2
    simp at h1 h2
    have hEq := hb (prof (cst w) id)
    rw [h1, h2] at hEq
    have hD : g w 1 - g w 0 ≠ 0 := by
      simpa [rootDifference, childDifference, hgM] using he
    have : M'.child w * (g w 1 - g w 0) = M.root * (g w 1 - g w 0) := by linarith
    exact mul_right_cancel₀ hD this

/-- A valid gap always supplies a nonzero direction difference too. -/
public theorem exists_childDifference_ne_zero {lam : ℝ} {g : Fin 2 → Fin 2 → ℝ}
    (hlam : 0 < lam) (hg : ValidGap lam g) (orientation : Orientation) :
    ∃ i, childDifference orientation g i ≠ 0 := by
  obtain ⟨-, -, -, ⟨y, hy⟩, ⟨x, hx⟩⟩ := hg
  cases orientation
  · exact ⟨x, by
      simp only [childDifference]
      intro h
      rw [h] at hx
      simp at hx
      linarith⟩
  · exact ⟨y, by
      simp only [childDifference]
      intro h
      rw [h] at hy
      simp at hy
      linarith⟩

public theorem eq_other_of_ne {i z : Fin 2} (h : i ≠ z) : i = other z := by
  fin_cases i <;> fin_cases z <;> simp_all [other]

/-- On a binary index, one vanishing and one nonvanishing entry is exactly the
source's "exactly one flat" condition. -/
public theorem exactlyOneFlat_of {d : Fin 2 → ℝ} {z i : Fin 2}
    (hz : d z = 0) (hi : d i ≠ 0) : ExactlyOneFlat d := by
  refine ⟨z, hz, ?_⟩
  have hiz : i = other z := eq_other_of_ne (fun h ↦ hi (by rw [h]; exact hz))
  rwa [← hiz]

/-! ## The unread coordinate

The two reading profiles show which coordinates the criterion *can* see. The
converse is what the criterion's companion clause rests on: when a direction
difference vanishes, the coordinate it would have read is invisible to **all
sixteen** profiles, so it may be moved freely without disturbing any behaviour.
-/

public theorem fin_two_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-- One transformed factor summed against an arbitrary weight vector. The local
map enters only through the two values it takes. -/
public theorem sum_factor_mul (p : ℝ) (f : Fin 2 → Fin 2) (h : Fin 2 → ℝ) :
    ∑ r : Fin 2, interventionFactor p f r * h r = (1 - p) * h (f 0) + p * h (f 1) := by
  unfold interventionFactor bernoulli
  rcases fin_two_eq_zero_or_one (f 0) with h0 | h0 <;>
    rcases fin_two_eq_zero_or_one (f 1) with h1 | h1 <;>
      simp [Fin.sum_univ_two, h0, h1] <;> ring

/-- A constant weight vector hides the parameter entirely. -/
public theorem sum_factor_mul_of_const (p : ℝ) (f : Fin 2 → Fin 2) (h : Fin 2 → ℝ)
    (hc : h 1 = h 0) : ∑ r : Fin 2, interventionFactor p f r * h r = h 0 := by
  rw [sum_factor_mul]
  rcases fin_two_eq_zero_or_one (f 0) with h0 | h0 <;>
    rcases fin_two_eq_zero_or_one (f 1) with h1 | h1 <;>
      simp only [h0, h1, hc] <;> ring

public theorem transform_eq_forward {M : PairModel} (hg : M.orientation = Orientation.forward)
    (g : Fin 2 → Fin 2 → ℝ) (profile : Profile) :
    M.transform g profile =
      ∑ x : Fin 2, interventionFactor M.root (profile 0) x *
        ∑ y : Fin 2, interventionFactor (M.child x) (profile 1) y * g x y := by
  unfold PairModel.transform PairModel.jointProb
  simp only [hg, Finset.mul_sum, mul_assoc]

public theorem transform_eq_reverse {M : PairModel} (hg : M.orientation = Orientation.reverse)
    (g : Fin 2 → Fin 2 → ℝ) (profile : Profile) :
    M.transform g profile =
      ∑ y : Fin 2, interventionFactor M.root (profile 1) y *
        ∑ x : Fin 2, interventionFactor (M.child y) (profile 0) x * g x y := by
  unfold PairModel.transform PairModel.jointProb
  simp only [hg]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

/-- **The unread coordinate.** If the direction difference at `z` vanishes, then
two same-orientation models agreeing on the root and on the *other* child
coordinate agree on every one of the sixteen transform coordinates, whatever
their `child z` values are. -/
public theorem behaviorEq_of_childDifference_eq_zero {M M' : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {z : Fin 2} (hgr : M'.orientation = M.orientation)
    (hroot : M'.root = M.root)
    (hother : M'.child (other z) = M.child (other z))
    (hd : childDifference M.orientation g z = 0) :
    BehaviorEq g M M' := by
  intro profile
  have hfree : ∀ (c c' : ℝ) (f : Fin 2 → Fin 2) (h : Fin 2 → ℝ), h 1 = h 0 →
      ∑ r : Fin 2, interventionFactor c f r * h r = ∑ r : Fin 2, interventionFactor c' f r * h r := by
    intro c c' f h hc
    rw [sum_factor_mul_of_const _ _ _ hc, sum_factor_mul_of_const _ _ _ hc]
  have hsame : ∀ i : Fin 2, i ≠ z → M'.child i = M.child i := by
    intro i hi
    rw [eq_other_of_ne hi]
    exact hother
  cases hgM : M.orientation with
  | forward =>
    have hg' : M'.orientation = Orientation.forward := by rw [hgr, hgM]
    have hconst : g z 1 = g z 0 := by
      have := hd
      rw [hgM] at this
      simp only [childDifference] at this
      linarith
    rw [transform_eq_forward hgM, transform_eq_forward hg', hroot]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hxz : x = z
    · subst hxz
      rw [hfree (M.child x) (M'.child x) (profile 1) (g x) hconst]
    · rw [hsame x hxz]
  | reverse =>
    have hg' : M'.orientation = Orientation.reverse := by rw [hgr, hgM]
    have hconst : g 1 z = g 0 z := by
      have := hd
      rw [hgM] at this
      simp only [childDifference] at this
      linarith
    rw [transform_eq_reverse hgM, transform_eq_reverse hg', hroot]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    by_cases hyz : y = z
    · subst hyz
      rw [hfree (M.child y) (M'.child y) (profile 0) (fun x ↦ g x y) hconst]
    · rw [hsame y hyz]

@[simp] public theorem other_ne (z : Fin 2) : other z ≠ z := by
  fin_cases z <;> simp

/-! ## Closed forms

Both charts collapse to a two-step convex combination once `sum_factor_mul` is
applied twice. A profile enters only through the four index values it names.
-/

public theorem transform_forward_closed {M : PairModel}
    (hg : M.orientation = Orientation.forward) (g : Fin 2 → Fin 2 → ℝ) (profile : Profile) :
    M.transform g profile =
      (1 - M.root) * ((1 - M.child (profile 0 0)) * g (profile 0 0) (profile 1 0)
          + M.child (profile 0 0) * g (profile 0 0) (profile 1 1))
        + M.root * ((1 - M.child (profile 0 1)) * g (profile 0 1) (profile 1 0)
          + M.child (profile 0 1) * g (profile 0 1) (profile 1 1)) := by
  rw [transform_eq_forward hg]
  have hin : ∀ x : Fin 2, (∑ y : Fin 2, interventionFactor (M.child x) (profile 1) y * g x y)
      = (1 - M.child x) * g x (profile 1 0) + M.child x * g x (profile 1 1) := by
    intro x; rw [sum_factor_mul]
  simp only [hin]
  rw [sum_factor_mul M.root (profile 0)
    (fun x ↦ (1 - M.child x) * g x (profile 1 0) + M.child x * g x (profile 1 1))]

public theorem transform_reverse_closed {M : PairModel}
    (hg : M.orientation = Orientation.reverse) (g : Fin 2 → Fin 2 → ℝ) (profile : Profile) :
    M.transform g profile =
      (1 - M.root) * ((1 - M.child (profile 1 0)) * g (profile 0 0) (profile 1 0)
          + M.child (profile 1 0) * g (profile 0 1) (profile 1 0))
        + M.root * ((1 - M.child (profile 1 1)) * g (profile 0 0) (profile 1 1)
          + M.child (profile 1 1) * g (profile 0 1) (profile 1 1)) := by
  rw [transform_eq_reverse hg]
  have hin : ∀ y : Fin 2, (∑ x : Fin 2, interventionFactor (M.child y) (profile 0) x * g x y)
      = (1 - M.child y) * g (profile 0 0) y + M.child y * g (profile 0 1) y := by
    intro y; rw [sum_factor_mul]
  simp only [hin]
  rw [sum_factor_mul M.root (profile 1)
    (fun y ↦ (1 - M.child y) * g (profile 0 0) y + M.child y * g (profile 0 1) y)]

/-! ## Building the opposite-orientation mate

Two flat lines make the gap table constant off one entry. On such a table a
forward model and a reverse model collide as soon as the reverse root is the
forward model's *read* child coordinate and the reverse model's own read
coordinate is the forward root. The remaining reverse coordinate is free, which
is why the criterion only asks the root's companion set to be inhabited.
-/

/-- Row `z` of the gap table is constant. -/
private theorem row_const {g : Fin 2 → Fin 2 → ℝ} {z w : Fin 2}
    (hz : g z 1 - g z 0 = 0) : ∀ y, g z y = g z w := by
  have h : g z 1 = g z 0 := by linarith
  intro y; fin_cases y <;> fin_cases w <;> simp_all

/-- Column `w` of the gap table is constant. -/
private theorem col_const {g : Fin 2 → Fin 2 → ℝ} {z w : Fin 2}
    (hw : g 1 w - g 0 w = 0) : ∀ x, g x w = g z w := by
  have h : g 1 w = g 0 w := by linarith
  intro x; fin_cases x <;> fin_cases z <;> simp_all

/-- A forward model and a reverse model with the crossed readings agree on all
sixteen coordinates. The reverse model's coordinate at `w` never appears. -/
public theorem behaviorEq_crossed_forward {M M' : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {z w : Fin 2}
    (hgM : M.orientation = Orientation.forward) (hgM' : M'.orientation = Orientation.reverse)
    (hz : g z 1 - g z 0 = 0) (hw : g 1 w - g 0 w = 0)
    (hroot : M'.root = M.child (other z))
    (hcw : M'.child (other w) = M.root) :
    BehaviorEq g M M' := by
  intro profile
  have e1 : ∀ y, g z y = g z w := row_const hz
  have e2 : ∀ x, g x w = g z w := col_const hw
  rw [transform_forward_closed hgM, transform_reverse_closed hgM']
  rcases fin_two_eq_zero_or_one z with hzv | hzv <;> subst hzv <;>
    rcases fin_two_eq_zero_or_one w with hwv | hwv <;> subst hwv <;>
    simp only [other_zero, other_one] at hroot hcw <;>
    rcases fin_two_eq_zero_or_one (profile 0 0) with ha | ha <;>
    rcases fin_two_eq_zero_or_one (profile 0 1) with hb | hb <;>
    rcases fin_two_eq_zero_or_one (profile 1 0) with hu | hu <;>
    rcases fin_two_eq_zero_or_one (profile 1 1) with hv | hv <;>
    simp only [ha, hb, hu, hv, hroot, hcw, e1, e2] <;>
    ring

/-- The mirror of `behaviorEq_crossed_forward`: a reverse model and a forward
model with the crossed readings agree on all sixteen coordinates. -/
public theorem behaviorEq_crossed_reverse {M M' : PairModel}
    {g : Fin 2 → Fin 2 → ℝ} {z w : Fin 2}
    (hgM : M.orientation = Orientation.reverse) (hgM' : M'.orientation = Orientation.forward)
    (hz : g 1 z - g 0 z = 0) (hw : g w 1 - g w 0 = 0)
    (hroot : M'.root = M.child (other z))
    (hcw : M'.child (other w) = M.root) :
    BehaviorEq g M M' := by
  intro profile
  have e1 : ∀ x, g x z = g w z := col_const (z := w) (w := z) hz
  have e2 : ∀ y, g w y = g w z := row_const (z := w) (w := z) hw
  rw [transform_reverse_closed hgM, transform_forward_closed hgM']
  rcases fin_two_eq_zero_or_one z with hzv | hzv <;> subst hzv <;>
    rcases fin_two_eq_zero_or_one w with hwv | hwv <;> subst hwv <;>
    simp only [other_zero, other_one] at hroot hcw <;>
    rcases fin_two_eq_zero_or_one (profile 0 0) with ha | ha <;>
    rcases fin_two_eq_zero_or_one (profile 0 1) with hb | hb <;>
    rcases fin_two_eq_zero_or_one (profile 1 0) with hu | hu <;>
    rcases fin_two_eq_zero_or_one (profile 1 1) with hv | hv <;>
    simp only [ha, hb, hu, hv, hroot, hcw, e1, e2] <;>
    ring

/-- The other orientation. -/
@[expose] public def otherOrientation : Orientation → Orientation
  | Orientation.forward => Orientation.reverse
  | Orientation.reverse => Orientation.forward

@[simp] public theorem otherOrientation_ne (gr : Orientation) : otherOrientation gr ≠ gr := by
  cases gr <;> simp [otherOrientation]

/-! ## The bridge to the causal kernel

The module note above records that the arithmetic here has the same *shape* as
`AISafetyAtlas.Causal.Model`'s and that nothing proves them equal. Since
2026-08-21 something does: a chart point in the unit box is a `Model`, its
`Model.factor` **is** `interventionFactor`, its `Model.jointProb` is
`PairModel.jointProb`, and its `Model.Δ` is `PairModel.transform`.

This does not retire the chart. The two reasons the parametrization review gave
still stand: `PairModel` is `@[ext]` on three numbers where `Model.ext` needs a
function-valued table, so quantifying over `Model` would adjudicate a different
question than the one MAIS issue #4 asks in chart coordinates; and sign agreement
in the O31 chain is a decision-layer notion. What the bridge removes is the third
thing — the possibility that the two arithmetics silently disagree. -/

open AISafetyAtlas.Causal

/-- The bounds a `Model`'s tables need. -/
@[expose] public def PairModel.InUnitBox (M : PairModel) : Prop :=
  (0 ≤ M.root ∧ M.root ≤ 1) ∧ ∀ i, 0 ≤ M.child i ∧ M.child i ≤ 1

/-- Every chart point of the source's family is in the unit box. -/
public theorem PairModel.inUnitBox_of_valid {lam : ℝ} {M : PairModel}
    (h : M.Valid lam) : M.InUnitBox := by
  obtain ⟨hlam, -, ⟨hr0, hr1⟩, hchild, -⟩ := h
  exact ⟨⟨by linarith, by linarith⟩,
    fun i ↦ ⟨by have := (hchild i).1; linarith, by have := (hchild i).2; linarith⟩⟩

/-- Which of the two variables the orientation makes the root. -/
@[expose] public def PairModel.rootIndex (M : PairModel) : Fin 2 :=
  match M.orientation with
  | .forward => 0
  | .reverse => 1

/-- The Bernoulli parameter each variable carries at an assignment. -/
@[expose] public noncomputable def PairModel.param (M : PairModel)
    (v : Fin 2 → Fin 2) (c : Fin 2) : ℝ :=
  if c = M.rootIndex then M.root else M.child (v M.rootIndex)

/-- The one-edge graph the orientation names. -/
@[expose] public def PairModel.parentMap (M : PairModel) : Fin 2 → Finset (Fin 2) :=
  fun c ↦ if c = M.rootIndex then ∅ else {M.rootIndex}

/-- **A chart point is a causal model.** -/
@[expose] public noncomputable def PairModel.toModel (M : PairModel) (h : M.InUnitBox) :
    Model (Fin 2) (binaryDim (Fin 2)) ℝ where
  dim_pos := fun _ ↦ by norm_num
  parents := M.parentMap
  acyclic := by
    refine ⟨fun c ↦ if c = M.rootIndex then 0 else 1, fun c p hp ↦ ?_⟩
    by_cases hc : c = M.rootIndex
    · simp [PairModel.parentMap, hc] at hp
    · simp only [PairModel.parentMap, hc, if_false, Finset.mem_singleton] at hp
      simp [hp, hc]
  cpt := fun c a v ↦ bernoulli (M.param v c) a
  cpt_parents := by
    intro c a v w hvw
    by_cases hc : c = M.rootIndex
    · simp [PairModel.param, hc]
    · have : v M.rootIndex = w M.rootIndex :=
        hvw M.rootIndex (by simp [PairModel.parentMap, hc])
      simp [PairModel.param, hc, this]
  cpt_nonneg := by
    intro c a v
    have hp : 0 ≤ M.param v c ∧ M.param v c ≤ 1 := by
      by_cases hc : c = M.rootIndex
      · simpa [PairModel.param, hc] using h.1
      · simpa [PairModel.param, hc] using h.2 (v M.rootIndex)
    have hbin : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
    rcases hbin a with rfl | rfl <;> simp [bernoulli] <;> linarith [hp.1, hp.2]
  cpt_sum := by
    intro c v
    simp [bernoulli, Fin.sum_univ_two]

/-- **`Model.factor` is `interventionFactor`.** RE24 equation (1) and this
module's Bernoulli factor are the same arithmetic, not merely the same shape. -/
public theorem PairModel.factor_toModel (M : PairModel) (h : M.InUnitBox)
    (σ : Profile) (v : Fin 2 → Fin 2) (c : Fin 2) :
    (M.toModel h).factor σ v c = interventionFactor (M.param v c) (σ c) (v c) := rfl

/-- **The two interventional joints agree.** -/
public theorem PairModel.jointProb_toModel (M : PairModel) (h : M.InUnitBox)
    (σ : Profile) (v : Fin 2 → Fin 2) :
    (M.toModel h).jointProb σ v = M.jointProb σ (v 0) (v 1) := by
  rw [Model.jointProb, Fin.prod_univ_two, M.factor_toModel h, M.factor_toModel h]
  cases hM : M.orientation
  · simp [PairModel.jointProb, hM, PairModel.param, PairModel.rootIndex]
  · simp [PairModel.jointProb, hM, PairModel.param, PairModel.rootIndex, mul_comm]

/-- **And so do the two behavioural transforms**, which is the object MAIS
issue #4's criterion is stated over. -/
public theorem PairModel.Δ_toModel (M : PairModel) (h : M.InUnitBox)
    (g : Fin 2 → Fin 2 → ℝ) (σ : Profile) :
    (M.toModel h).Δ (fun v ↦ g (v 0) (v 1)) σ = M.transform g σ := by
  rw [Model.Δ, ← Equiv.sum_comp finFunctionFinEquiv.symm]
  simp [PairModel.transform, PairModel.jointProb_toModel, Fin.sum_univ_four,
    Fin.sum_univ_two, finFunctionFinEquiv]
  ring

/-! ## Bridge to the printed two-variable margin class -/

/-- A normalized binary utility whose gap is the supplied two-variable table. -/
@[expose] public noncomputable def gapUtility (g : Fin 2 → Fin 2 → ℝ)
    (d : Bool) (v : Assignment (Fin 2) (binaryDim (Fin 2))) : ℝ :=
  if d then (1 + g (v 0) (v 1)) / 2 else (1 - g (v 0) (v 1)) / 2

/-- The source skeleton associated with a valid utility-gap table: no variables
are observed and both chance variables are utility parents. -/
@[expose] public noncomputable def pairSkeleton (g : Fin 2 → Fin 2 → ℝ)
    (hg : ∀ x y, |g x y| ≤ 1) : Skeleton (Fin 2) (binaryDim (Fin 2)) Bool ℝ where
  observed := ∅
  utilityParents := Finset.univ
  utility := gapUtility g
  utility_parents := by
    intro d v w h
    have hvw : v = w := funext fun c ↦ h c (Finset.mem_univ c)
    rw [hvw]
  utility_mem_unitInterval := by
    intro d v
    have hb := (abs_le.mp (hg (v 0) (v 1)))
    cases d <;> simp [gapUtility] <;> constructor <;> linarith

@[simp] public theorem pairSkeleton_observed (g : Fin 2 → Fin 2 → ℝ)
    (hg : ∀ x y, |g x y| ≤ 1) : (pairSkeleton g hg).observed = ∅ := rfl

@[simp] public theorem pairSkeleton_utilityParents (g : Fin 2 → Fin 2 → ℝ)
    (hg : ∀ x y, |g x y| ≤ 1) : (pairSkeleton g hg).utilityParents = Finset.univ := rfl

/-- The canonical normalized utility realizes exactly the supplied gap. -/
public theorem pairSkeleton_gap (g : Fin 2 → Fin 2 → ℝ)
    (hg : ∀ x y, |g x y| ≤ 1) :
    (pairSkeleton g hg).gap = fun v ↦ g (v 0) (v 1) := by
  funext v
  simp [Skeleton.gap, pairSkeleton, gapUtility]
  ring

/-- The canonical skeleton with its bound proof read from `ValidGap`. -/
@[expose] public noncomputable def pairSkeletonOfValid {lam : ℝ}
    (g : Fin 2 → Fin 2 → ℝ) (hg : ValidGap lam g) :
    Skeleton (Fin 2) (binaryDim (Fin 2)) Bool ℝ :=
  pairSkeleton g (fun x y ↦ (hg.1 x y).2)

@[simp] public theorem pairSkeletonOfValid_gap {lam : ℝ}
    (g : Fin 2 → Fin 2 → ℝ) (hg : ValidGap lam g) :
    (pairSkeletonOfValid g hg).gap = fun v ↦ g (v 0) (v 1) :=
  pairSkeleton_gap g _

/-- An assignment with explicitly named values for the two variables. -/
@[expose] public def pairAssignment (x y : Fin 2) : Assignment (Fin 2) (binaryDim (Fin 2)) :=
  fun c ↦ if c = 0 then x else y

@[simp] public theorem pairAssignment_zero (x y : Fin 2) : pairAssignment x y 0 = x := by
  simp [pairAssignment]

@[simp] public theorem pairAssignment_one (x y : Fin 2) : pairAssignment x y 1 = y := by
  simp [pairAssignment]

/-- Every Bernoulli parameter read by the kernel model stays in the printed
margin interval. -/
public theorem PairModel.param_mem_marginInterval {lam : ℝ} {M : PairModel}
    (hM : M.Valid lam) (v : Fin 2 → Fin 2) (c : Fin 2) :
    InMarginInterval lam (M.param v c) := by
  by_cases hc : c = M.rootIndex
  · simpa [PairModel.param, hc] using hM.2.2.1
  · simpa [PairModel.param, hc] using hM.2.2.2.1 (v M.rootIndex)

public theorem PairModel.toModel_printedM1 {lam : ℝ} {M : PairModel}
    (hM : M.Valid lam) :
    Skeleton.PrintedM1 (M.toModel (PairModel.inUnitBox_of_valid hM)) lam := by
  intro c v
  simpa [PairModel.toModel, bernoulli, InMarginInterval] using
    M.param_mem_marginInterval hM v c

public theorem PairModel.toModel_printedM4 {lam : ℝ} {M : PairModel}
    (hM : M.Valid lam) :
    Skeleton.PrintedM4 (M.toModel (PairModel.inUnitBox_of_valid hM)) lam := by
  intro c p hp
  have hc : c ≠ M.rootIndex := by
    intro hc
    simp [PairModel.toModel, PairModel.parentMap, hc] at hp
  have hpr : p = M.rootIndex := by
    simpa [PairModel.toModel, PairModel.parentMap, hc] using hp
  subst p
  refine ⟨fun _ ↦ 0, ?_⟩
  simp only [PairModel.toModel, bernoulli, if_pos, PairModel.param, hc, if_false]
  have hedge := hM.2.2.2.2
  rw [abs_sub_comm] at hedge
  simpa using hedge

public theorem pairSkeletonOfValid_m2 {lam : ℝ} {g : Fin 2 → Fin 2 → ℝ}
    (hg : ValidGap lam g) : (pairSkeletonOfValid g hg).M2 lam := by
  intro v
  rw [pairSkeletonOfValid_gap]
  exact (hg.1 (v 0) (v 1)).1

public theorem pairSkeletonOfValid_m3 {lam : ℝ} {g : Fin 2 → Fin 2 → ℝ}
    (hg : ValidGap lam g) : (pairSkeletonOfValid g hg).M3 := by
  intro w
  obtain ⟨xp, yp, hp⟩ := hg.2.1
  obtain ⟨xm, ym, hm⟩ := hg.2.2.1
  refine ⟨pairAssignment xp yp, pairAssignment xm ym, ?_, ?_, ?_, ?_⟩
  · simp [pairSkeletonOfValid]
  · simp [pairSkeletonOfValid]
  · simpa using hp
  · simpa using hm

public theorem pairSkeletonOfValid_m6 {lam : ℝ} {g : Fin 2 → Fin 2 → ℝ}
    (hg : ValidGap lam g) : (pairSkeletonOfValid g hg).M6 lam := by
  intro j _
  fin_cases j
  · obtain ⟨y, hy⟩ := hg.2.2.2.1
    refine ⟨pairAssignment 0 y, 1, 0, by decide, ?_⟩
    simpa [Function.update, pairAssignment] using hy
  · obtain ⟨x, hx⟩ := hg.2.2.2.2
    refine ⟨pairAssignment x 0, 1, 0, by decide, ?_⟩
    simpa [Function.update, pairAssignment] using hx

public theorem PairModel.pairSkeletonOfValid_printedM5 {lam : ℝ}
    {g : Fin 2 → Fin 2 → ℝ} (hg : ValidGap lam g) {M : PairModel}
    (hM : M.Valid lam) :
    (pairSkeletonOfValid g hg).PrintedM5
      (M.toModel (PairModel.inUnitBox_of_valid hM)) := by
  constructor
  · simp only [pairSkeletonOfValid, pairSkeleton_utilityParents,
      pairSkeleton_observed, Finset.union_empty]
    rw [Model.ancestors_eq_univ_iff]
    intro t ht _
    exact Finset.univ_subset_iff.mp ht
  · simp [pairSkeletonOfValid]

/-- A valid chart point is a member of the printed kernel margin class. -/
public theorem PairModel.toModel_marginClass {lam : ℝ} {g : Fin 2 → Fin 2 → ℝ}
    (hg : ValidGap lam g) {M : PairModel} (hM : M.Valid lam) :
    (pairSkeletonOfValid g hg).MarginClass
      (M.toModel (PairModel.inUnitBox_of_valid hM)) lam := by
  rw [Skeleton.marginClass_iff_printed]
  exact ⟨⟨hM.1, hM.2.1⟩, M.toModel_printedM1 hM,
    pairSkeletonOfValid_m2 hg, pairSkeletonOfValid_m3 hg,
    M.toModel_printedM4 hM, M.pairSkeletonOfValid_printedM5 hg hM,
    pairSkeletonOfValid_m6 hg⟩

/-- Chart transform equality is exactly kernel behavioral equality for the
canonical source skeleton. This closes both directions rather than merely
transporting a checked collision. -/
public theorem behaviorEq_iff_kernel {lam : ℝ} {g : Fin 2 → Fin 2 → ℝ}
    (hg : ValidGap lam g) {M M' : PairModel} (hM : M.Valid lam) (hM' : M'.Valid lam) :
    BehaviorEq g M M' ↔
      (pairSkeletonOfValid g hg).BehaviorEq
        (M.toModel (PairModel.inUnitBox_of_valid hM))
        (M'.toModel (PairModel.inUnitBox_of_valid hM')) := by
  constructor
  · intro hchart
    apply Skeleton.behaviorEq_of_observed_eq_empty rfl
    rw [Model.Δmix_eq_on_probMixture_iff]
    intro σ
    rw [pairSkeletonOfValid_gap, M.Δ_toModel, M'.Δ_toModel]
    exact hchart σ
  · intro hkernel σ
    have hmix : ∀ mix : ProbMixture (Fin 2) (binaryDim (Fin 2)) ℝ,
        (M.toModel (PairModel.inUnitBox_of_valid hM)).Δmix
            (pairSkeletonOfValid g hg).gap mix.1 =
          (M'.toModel (PairModel.inUnitBox_of_valid hM')).Δmix
            (pairSkeletonOfValid g hg).gap mix.1 := by
      intro mix
      have h := hkernel ∅ (by simp) (fun _ ↦ 0) mix
      simpa [Model.Δmask_empty] using h
    have hdet :=
      (Model.Δmix_eq_on_probMixture_iff
        (M.toModel (PairModel.inUnitBox_of_valid hM))
        (M'.toModel (PairModel.inUnitBox_of_valid hM'))
        (pairSkeletonOfValid g hg).gap).mp hmix σ
    rw [pairSkeletonOfValid_gap, M.Δ_toModel, M'.Δ_toModel] at hdet
    exact hdet

/-- The chart singleton fibre is the kernel behavioral fibre restricted to the
two one-edge charts that constitute the printed family. -/
public theorem hasSingletonFibre_iff_kernel {lam : ℝ} {g : Fin 2 → Fin 2 → ℝ}
    (hg : ValidGap lam g) {M : PairModel} (hM : M.Valid lam) :
    HasSingletonFibre g lam M ↔
      ∀ M' : PairModel, ∀ hM' : M'.Valid lam,
        (pairSkeletonOfValid g hg).BehaviorEq
          (M.toModel (PairModel.inUnitBox_of_valid hM))
          (M'.toModel (PairModel.inUnitBox_of_valid hM')) → M' = M := by
  constructor
  · intro hf M' hM' hbeh
    exact hf M' hM' ((behaviorEq_iff_kernel hg hM hM').mpr hbeh)
  · intro hf M' hM' hbeh
    exact hf M' hM' ((behaviorEq_iff_kernel hg hM hM').mp hbeh)

/-! ## The chart is onto the printed family

`toModel_marginClass` puts every chart point inside `𝕄₂(λ)`. A singleton-fibre
claim needs the converse. `HasSingletonFibre` quantifies over `PairModel`, and
`prob:starter-set`(a) asks when the fibre `{M' : 𝚫_{M'} = 𝚫_M}` is a singleton
*in `𝕄₂(λ)`*. Identification claims get easier as the comparison class shrinks,
so a chart-scope singleton is print's singleton only if the chart reaches every
model of the family. `def:twovar` says it does — three parameters and one binary
structural choice — and this section proves it, closing the last step between
`maisO34_exactFiberCandidate` and the printed question.
-/

/-- The root index an orientation names, read without a chart point. -/
@[expose] public def Orientation.rootIndex : Orientation → Fin 2
  | .forward => 0
  | .reverse => 1

public theorem PairModel.rootIndex_eq (M : PairModel) :
    M.rootIndex = M.orientation.rootIndex := by
  cases M with
  | mk gr _ _ => cases gr <;> rfl

/-- The one-edge graph an orientation names. -/
@[expose] public def Orientation.parents (gr : Orientation) : Fin 2 → Finset (Fin 2) :=
  fun c ↦ if c = gr.rootIndex then ∅ else {gr.rootIndex}

public theorem PairModel.parentMap_eq (M : PairModel) :
    M.parentMap = M.orientation.parents := by
  funext c
  simp [PairModel.parentMap, Orientation.parents, M.rootIndex_eq]

/-- **Every binary model carrying an edge carries one of the two printed
graphs.** On two vertices acyclicity leaves no third option: a self-parent is
excluded outright and both arrows at once would close a cycle. -/
public theorem exists_orientation_parents
    {N : Model (Fin 2) (binaryDim (Fin 2)) ℝ} (hedge : ∃ c p, p ∈ N.parents c) :
    ∃ gr : Orientation, N.parents = gr.parents := by
  obtain ⟨rank, hrank⟩ := N.acyclic
  have hno : ¬ ((0 : Fin 2) ∈ N.parents 1 ∧ (1 : Fin 2) ∈ N.parents 0) := by
    rintro ⟨h1, h2⟩
    exact lt_irrefl _ (lt_trans (hrank 1 0 h1) (hrank 0 1 h2))
  have h00 : (0 : Fin 2) ∉ N.parents 0 := N.notMem_parents_self 0
  have h11 : (1 : Fin 2) ∉ N.parents 1 := N.notMem_parents_self 1
  by_cases h01 : (0 : Fin 2) ∈ N.parents 1
  · refine ⟨.forward, ?_⟩
    have h10 : (1 : Fin 2) ∉ N.parents 0 := fun hh ↦ hno ⟨h01, hh⟩
    funext c
    fin_cases c <;> ext x <;> fin_cases x <;>
      simp_all [Orientation.parents, Orientation.rootIndex]
  · refine ⟨.reverse, ?_⟩
    have h1e : ∀ x : Fin 2, x ∉ N.parents 1 := by
      intro x
      fin_cases x
      · exact h01
      · exact h11
    obtain ⟨c, p, hp⟩ := hedge
    have hc : c = 0 := by
      fin_cases c
      · rfl
      · exact absurd hp (h1e p)
    subst hc
    have hp1 : p = 1 := by
      fin_cases p
      · exact absurd hp h00
      · rfl
    subst hp1
    funext d
    fin_cases d <;> ext x <;> fin_cases x <;>
      simp_all [Orientation.parents, Orientation.rootIndex]

/-- The chart point a kernel model's own tables name, at a chosen orientation. -/
@[expose] public noncomputable def PairModel.ofModel (gr : Orientation)
    (N : Model (Fin 2) (binaryDim (Fin 2)) ℝ) : PairModel where
  orientation := gr
  root := N.cpt gr.rootIndex 1 (fun _ ↦ 0)
  child := fun y ↦ N.cpt (other gr.rootIndex) 1
    (Function.update (fun _ ↦ (0 : Fin 2)) gr.rootIndex y)

private theorem cpt_zero_eq {N : Model (Fin 2) (binaryDim (Fin 2)) ℝ}
    (c : Fin 2) (v : Fin 2 → Fin 2) : N.cpt c 0 v = 1 - N.cpt c 1 v := by
  have hsum := N.cpt_sum c v
  rw [Fin.sum_univ_two] at hsum
  linarith

private theorem cpt_root_congr {gr : Orientation}
    {N : Model (Fin 2) (binaryDim (Fin 2)) ℝ} (hp : N.parents = gr.parents)
    (a : Fin 2) (v w : Fin 2 → Fin 2) :
    N.cpt gr.rootIndex a v = N.cpt gr.rootIndex a w := by
  refine N.cpt_parents _ _ _ _ ?_
  intro p hmem
  rw [hp] at hmem
  simp [Orientation.parents] at hmem

private theorem cpt_child_congr {gr : Orientation}
    {N : Model (Fin 2) (binaryDim (Fin 2)) ℝ} (hp : N.parents = gr.parents)
    (a : Fin 2) (v w : Fin 2 → Fin 2) (hvw : v gr.rootIndex = w gr.rootIndex) :
    N.cpt (other gr.rootIndex) a v = N.cpt (other gr.rootIndex) a w := by
  refine N.cpt_parents _ _ _ _ ?_
  intro p hmem
  rw [hp] at hmem
  simp only [Orientation.parents, if_neg (other_ne gr.rootIndex),
    Finset.mem_singleton] at hmem
  subst hmem
  exact hvw

/-- **The chart is onto the printed family.** A model whose graph is one of the
two printed arrows is exactly the chart point its own tables name. -/
public theorem PairModel.toModel_ofModel {gr : Orientation}
    {N : Model (Fin 2) (binaryDim (Fin 2)) ℝ} (hp : N.parents = gr.parents)
    (h : (PairModel.ofModel gr N).InUnitBox) :
    (PairModel.ofModel gr N).toModel h = N := by
  refine Model.ext ?_ ?_
  · show (PairModel.ofModel gr N).parentMap = N.parents
    rw [PairModel.parentMap_eq, hp]
    rfl
  · funext c a v
    show bernoulli ((PairModel.ofModel gr N).param v c) a = N.cpt c a v
    have hri : (PairModel.ofModel gr N).rootIndex = gr.rootIndex :=
      (PairModel.ofModel gr N).rootIndex_eq
    have hpar : (PairModel.ofModel gr N).param v c = N.cpt c 1 v := by
      rw [PairModel.param, hri]
      by_cases hc : c = gr.rootIndex
      · rw [if_pos hc, hc]
        exact cpt_root_congr hp 1 _ _
      · rw [if_neg hc, eq_other_of_ne hc]
        exact cpt_child_congr hp 1 _ _ (by simp)
    rw [hpar]
    rcases fin_two_eq_zero_or_one a with rfl | rfl
    · simpa [bernoulli] using (cpt_zero_eq (N := N) c v).symm
    · simp [bernoulli]

/-- The chart coordinates read off a model of the printed class satisfy the
printed margins: `(M1)` gives both intervals and `(M4)` the edge strength. -/
public theorem PairModel.ofModel_valid {lam : ℝ} {g : Fin 2 → Fin 2 → ℝ}
    (hg : ValidGap lam g) {gr : Orientation}
    {N : Model (Fin 2) (binaryDim (Fin 2)) ℝ}
    (hN : (pairSkeletonOfValid g hg).MarginClass N lam)
    (hp : N.parents = gr.parents) :
    (PairModel.ofModel gr N).Valid lam := by
  rw [Skeleton.marginClass_iff_printed] at hN
  obtain ⟨⟨hlam0, hlam2⟩, hm1, -, -, hm4, -, -⟩ := hN
  refine ⟨hlam0, hlam2, hm1 _ _, fun i ↦ hm1 _ _, ?_⟩
  have hmem : gr.rootIndex ∈ N.parents (other gr.rootIndex) := by
    rw [hp]
    simp [Orientation.parents, other_ne gr.rootIndex]
  obtain ⟨w, hw⟩ := hm4 (other gr.rootIndex) gr.rootIndex hmem
  have hchild : ∀ y : Fin 2, (PairModel.ofModel gr N).child y
      = N.cpt (other gr.rootIndex) 1 (Function.update w gr.rootIndex y) := by
    intro y
    show N.cpt (other gr.rootIndex) 1
      (Function.update (fun _ ↦ (0 : Fin 2)) gr.rootIndex y) = _
    exact cpt_child_congr hp 1 _ _ (by simp)
  rw [hchild 1, hchild 0, abs_sub_comm]
  exact hw

/-- **Surjectivity, packaged.** Every model of the printed two-variable family is
`toModel` of a valid chart point. -/
public theorem exists_pairModel_toModel_eq {lam : ℝ} {g : Fin 2 → Fin 2 → ℝ}
    (hg : ValidGap lam g) {N : Model (Fin 2) (binaryDim (Fin 2)) ℝ}
    (hN : (pairSkeletonOfValid g hg).MarginClass N lam)
    (hedge : ∃ c p, p ∈ N.parents c) :
    ∃ P : PairModel, ∃ hP : P.Valid lam,
      P.toModel (PairModel.inUnitBox_of_valid hP) = N := by
  obtain ⟨gr, hp⟩ := exists_orientation_parents hedge
  exact ⟨PairModel.ofModel gr N, PairModel.ofModel_valid hg hN hp,
    PairModel.toModel_ofModel hp _⟩

/-- `ofModel` is a left inverse of `toModel`, so the chart is injective too. -/
public theorem PairModel.ofModel_toModel (P : PairModel) (h : P.InUnitBox) :
    PairModel.ofModel P.orientation (P.toModel h) = P := by
  refine PairModel.ext rfl ?_ ?_
  · show bernoulli (P.param (fun _ ↦ 0) P.orientation.rootIndex) 1 = P.root
    simp [bernoulli, PairModel.param, P.rootIndex_eq]
  · funext y
    show bernoulli (P.param (Function.update (fun _ ↦ (0 : Fin 2))
      P.orientation.rootIndex y) (other P.orientation.rootIndex)) 1 = P.child y
    simp [bernoulli, PairModel.param, P.rootIndex_eq, other_ne]

public theorem PairModel.toModel_injective {P Q : PairModel}
    {hP : P.InUnitBox} {hQ : Q.InUnitBox} (h : P.toModel hP = Q.toModel hQ) :
    P = Q := by
  have hpar : P.orientation.parents = Q.orientation.parents := by
    have : (P.toModel hP).parents = (Q.toModel hQ).parents := by rw [h]
    rwa [show (P.toModel hP).parents = P.parentMap from rfl,
      show (Q.toModel hQ).parents = Q.parentMap from rfl,
      PairModel.parentMap_eq, PairModel.parentMap_eq] at this
  have hor : P.orientation = Q.orientation := by
    cases hgP : P.orientation <;> cases hgQ : Q.orientation <;>
      first
        | rfl
        | (exfalso
           rw [hgP, hgQ] at hpar
           have := congrFun hpar 0
           simp [Orientation.parents, Orientation.rootIndex] at this)
  calc P = PairModel.ofModel P.orientation (P.toModel hP) := (P.ofModel_toModel hP).symm
    _ = PairModel.ofModel Q.orientation (Q.toModel hQ) := by rw [hor, h]
    _ = Q := Q.ofModel_toModel hQ

/-- **The chart singleton fibre is print's fibre.** `hasSingletonFibre_iff_kernel`
compares `M` against chart points; this compares it against every model of the
printed class carrying an edge, which is `𝕄₂(λ)` as `def:twovar` writes it. -/
public theorem hasSingletonFibre_iff_kernel_class {lam : ℝ} {g : Fin 2 → Fin 2 → ℝ}
    (hg : ValidGap lam g) {M : PairModel} (hM : M.Valid lam) :
    HasSingletonFibre g lam M ↔
      ∀ N : Model (Fin 2) (binaryDim (Fin 2)) ℝ,
        (pairSkeletonOfValid g hg).MarginClass N lam →
        (∃ c p, p ∈ N.parents c) →
        (pairSkeletonOfValid g hg).BehaviorEq
          (M.toModel (PairModel.inUnitBox_of_valid hM)) N →
        N = M.toModel (PairModel.inUnitBox_of_valid hM) := by
  constructor
  · intro hf N hNclass hNedge hbeh
    obtain ⟨P, hP, rfl⟩ := exists_pairModel_toModel_eq hg hNclass hNedge
    have hPM : P = M := hf P hP ((behaviorEq_iff_kernel hg hM hP).mpr hbeh)
    subst hPM
    rfl
  · intro hf M' hM' hbeh
    have hclass := PairModel.toModel_marginClass hg hM'
    have hedge : ∃ c p, p ∈ (M'.toModel (PairModel.inUnitBox_of_valid hM')).parents c := by
      refine ⟨other M'.orientation.rootIndex, M'.orientation.rootIndex, ?_⟩
      show M'.orientation.rootIndex ∈ M'.parentMap (other M'.orientation.rootIndex)
      rw [PairModel.parentMap_eq]
      simp [Orientation.parents, other_ne M'.orientation.rootIndex]
    exact PairModel.toModel_injective
      (hf _ hclass hedge ((behaviorEq_iff_kernel hg hM hM').mp hbeh))

/-! ## The companion set, quantifier-free

`prob:starter-set`(a) asks for the singleton condition as an *explicit
semialgebraic condition on `(u, θ)`*. Issue #4's criterion is written with two
clauses that quantify over the reals — `separatedValues lam t = {b}` and
`(separatedValues lam t).Nonempty` — and a condition carrying a real quantifier
is not visibly semialgebraic. Tarski–Seidenberg eliminates them in principle;
here they are eliminated by hand, which is cheaper and produces the explicit
inequalities print asks for.

`separatedValues lam t` is the margin box `[λ, 1-λ]` with the open interval
`(t-λ, t+λ)` removed, so it is the union of two closed intervals, disjoint
because `λ > 0`.
-/

/-- The companion set as the union of its two intervals. -/
public theorem separatedValues_eq_union (lam t : ℝ) :
    separatedValues lam t =
      Set.Icc lam (min (1 - lam) (t - lam)) ∪ Set.Icc (max lam (t + lam)) (1 - lam) := by
  ext s
  simp only [separatedValues, Set.mem_ofPred_eq, InMarginInterval, Set.mem_union,
    Set.mem_Icc, le_min_iff, max_le_iff]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, habs⟩
    rcases le_abs.mp habs with h | h
    · exact Or.inr ⟨⟨hlo, by linarith⟩, hhi⟩
    · exact Or.inl ⟨hlo, hhi, by linarith⟩
  · rintro (⟨hlo, hhi1, hhi2⟩ | ⟨⟨hlo1, hlo2⟩, hhi⟩)
    · exact ⟨⟨hlo, hhi1⟩, le_abs.mpr (Or.inr (by linarith))⟩
    · exact ⟨⟨hlo1, hhi⟩, le_abs.mpr (Or.inl (by linarith))⟩

/-- **The companion set is nonempty exactly on an explicit pair of half-planes.**
No real quantifier survives. -/
public theorem separatedValues_nonempty_iff {lam t : ℝ}
    (_hlam0 : 0 < lam) (hlam2 : lam < 1 / 2) :
    (separatedValues lam t).Nonempty ↔ 2 * lam ≤ t ∨ t ≤ 1 - 2 * lam := by
  rw [separatedValues_eq_union]
  constructor
  · rintro ⟨s, hs | hs⟩
    · simp only [Set.mem_Icc, le_min_iff] at hs
      exact Or.inl (by linarith [hs.1, hs.2.2])
    · simp only [Set.mem_Icc, max_le_iff] at hs
      exact Or.inr (by linarith [hs.1.2, hs.2])
  · rintro (h | h)
    · refine ⟨lam, Or.inl ?_⟩
      simp only [Set.mem_Icc, le_min_iff]
      exact ⟨le_refl _, by linarith, by linarith⟩
    · refine ⟨1 - lam, Or.inr ?_⟩
      simp only [Set.mem_Icc, max_le_iff]
      exact ⟨⟨by linarith, by linarith⟩, le_refl _⟩

/-- **The companion set is a singleton exactly on an explicit polynomial
condition**, and only when the margin exceeds `1/4`.

The two intervals are disjoint, so a singleton forces one to be empty and the
other to be a point. Both are nonempty whenever `4λ ≤ 1`, and a degenerate
survivor sits at an endpoint of the margin box. -/
public theorem separatedValues_eq_singleton_iff {lam t b : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2) :
    separatedValues lam t = {b} ↔
      1 < 4 * lam ∧ ((t = 2 * lam ∧ b = lam) ∨ (t = 1 - 2 * lam ∧ b = 1 - lam)) := by
  have hbox : lam < 1 - lam := by linarith
  rw [separatedValues_eq_union]
  constructor
  · intro hset
    have hmem : ∀ s : ℝ,
        s ∈ Set.Icc lam (min (1 - lam) (t - lam)) ∪ Set.Icc (max lam (t + lam)) (1 - lam) →
        s = b := by
      intro s hs
      have hb : s ∈ ({b} : Set ℝ) := hset ▸ hs
      simpa using hb
    have hA : 2 * lam ≤ t → lam ∈ Set.Icc lam (min (1 - lam) (t - lam)) := fun h ↦
      Set.mem_Icc.mpr ⟨le_refl lam, le_min (by linarith) (by linarith)⟩
    have hAtop : 2 * lam ≤ t →
        min (1 - lam) (t - lam) ∈ Set.Icc lam (min (1 - lam) (t - lam)) := fun h ↦
      Set.mem_Icc.mpr ⟨le_min (by linarith) (by linarith), le_refl _⟩
    have hB : t ≤ 1 - 2 * lam → (1 : ℝ) - lam ∈ Set.Icc (max lam (t + lam)) (1 - lam) :=
      fun h ↦ Set.mem_Icc.mpr ⟨max_le (by linarith) (by linarith), le_refl _⟩
    have hBbot : t ≤ 1 - 2 * lam →
        max lam (t + lam) ∈ Set.Icc (max lam (t + lam)) (1 - lam) := fun h ↦
      Set.mem_Icc.mpr ⟨le_refl _, max_le (by linarith) (by linarith)⟩
    have hside : 2 * lam ≤ t ∨ t ≤ 1 - 2 * lam := by
      obtain ⟨s, hs⟩ : (Set.Icc lam (min (1 - lam) (t - lam)) ∪
          Set.Icc (max lam (t + lam)) (1 - lam)).Nonempty := hset ▸ Set.singleton_nonempty b
      rcases hs with hs | hs
      · have h := Set.mem_Icc.mp hs
        exact Or.inl (by linarith [h.1, h.2.trans (min_le_right (1 - lam) (t - lam))])
      · have h := Set.mem_Icc.mp hs
        exact Or.inr (by linarith [(le_max_right lam (t + lam)).trans h.1, h.2])
    have hleft : 2 * lam ≤ t → t = 2 * lam ∧ b = lam := by
      intro h
      have h1 : lam = b := hmem lam (Or.inl (hA h))
      have h2 : min (1 - lam) (t - lam) = b := hmem _ (Or.inl (hAtop h))
      have hmin : min (1 - lam) (t - lam) = lam := h2.trans h1.symm
      rcases min_choice (1 - lam) (t - lam) with hc | hc
      · rw [hc] at hmin; exact absurd hmin (by linarith)
      · rw [hc] at hmin; exact ⟨by linarith, h1.symm⟩
    have hright : t ≤ 1 - 2 * lam → t = 1 - 2 * lam ∧ b = 1 - lam := by
      intro h
      have h3 : (1 : ℝ) - lam = b := hmem _ (Or.inr (hB h))
      have h4 : max lam (t + lam) = b := hmem _ (Or.inr (hBbot h))
      have hmax : max lam (t + lam) = 1 - lam := h4.trans h3.symm
      rcases max_choice lam (t + lam) with hc | hc
      · rw [hc] at hmax; exact absurd hmax (by linarith)
      · rw [hc] at hmax; exact ⟨by linarith, h3.symm⟩
    have hquarter : 1 < 4 * lam := by
      by_contra hcon
      have hq : 4 * lam ≤ 1 := not_lt.mp hcon
      rcases hside with h | h
      · obtain ⟨ht, hbv⟩ := hleft h
        have hB' : t ≤ 1 - 2 * lam := by linarith
        have h3 : (1 : ℝ) - lam = b := hmem _ (Or.inr (hB hB'))
        linarith [hbv.symm.trans h3.symm]
      · obtain ⟨ht, hbv⟩ := hright h
        have hA' : 2 * lam ≤ t := by linarith
        have h1 : lam = b := hmem lam (Or.inl (hA hA'))
        linarith [h1.trans hbv]
    exact ⟨hquarter, hside.imp hleft hright⟩
  · rintro ⟨hquarter, hcase⟩
    rcases hcase with ⟨ht, hb⟩ | ⟨ht, hb⟩ <;> subst ht <;> rw [hb]
    · have hmin : min (1 - lam) (2 * lam - lam) = lam := by
        rw [min_eq_right (by linarith)]; ring
      have hmax : max lam (2 * lam + lam) = 3 * lam := by
        rw [max_eq_right (by linarith)]; ring
      rw [hmin, hmax, Set.Icc_self,
        Set.Icc_eq_empty (by intro hc; linarith), Set.union_empty]
    · have hmin : min (1 - lam) (1 - 2 * lam - lam) = 1 - 3 * lam := by
        rw [min_eq_right (by linarith)]; ring
      have hmax : max lam (1 - 2 * lam + lam) = 1 - lam := by
        rw [max_eq_right (by linarith)]; ring
      rw [hmin, hmax, Set.Icc_self,
        Set.Icc_eq_empty (by intro hc; linarith), Set.empty_union]

/-- **Below margin `1/4` the companion clause of issue #4's criterion is
unsatisfiable.** `def:twovar`'s own computational project runs at `λ = 0.1`, so
in the regime the agenda simulates, the same-orientation criterion collapses to
its first disjunct: every child difference nonzero. -/
public theorem separatedValues_ne_singleton_of_le_quarter {lam t b : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2) (hq : 4 * lam ≤ 1) :
    separatedValues lam t ≠ {b} := fun hcon ↦
  absurd ((separatedValues_eq_singleton_iff hlam0 hlam2).mp hcon).1 (by linarith)

end AISafetyAtlas.Conjectures.BinaryPair
