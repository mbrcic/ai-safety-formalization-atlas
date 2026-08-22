module

public import AISafetyAtlas.Causal.Decision
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Discretizing the model space

MAIS-A2 `subsec:queries` says the analyst *"outputs `(Ĝ, θ̂)`"* and constrains
the output **value** — a graph and a table vector — while saying nothing about
the output **law**. `Causal.Query` renders a randomized analyst's output as a
`PMF`, which is countably supported, and that is a live scope axis: the infimum
defining the minimax risk then ranges over fewer estimators than print allows, so
a finite bound on the budget would be *stronger* than print's. It is not: the
lemmas below are what `Causal.measureMinimalBudget_eq_exactMinimalBudget` uses to
prove `N(ε)` is the same number under either reading, so the restriction costs
nothing. This module is that repair, and with it the query estimator's `PMF` vs.
measure axis is closed. Axes A, B and F elsewhere in the causal layer are still
open; see `docs/guide/causal-scope-open-work.md`.

This module carries the mathematical content of the repair. The observation is
that the printed error is bounded by `1` and, at a fixed graph, is `1`-Lipschitz
in the estimate under the sup-norm on tables, so an estimate may be **rounded**
without moving the error much — and a rounded model ranges over a countable set.
Since the risk is an infimum, an approximation that costs `O(ε)` for every
`ε > 0` costs nothing in the limit.

Rounding **down** is what makes this work on the simplex. Each conditional table
must be non-negative and sum to `1`; rounding every entry to a nearby multiple
of `ε` would break the sum. Rounding all but the last entry *down* and giving
the last the remainder keeps both: rounding down can only free mass, so the
remainder stays non-negative, and the sum is `1` by construction.

Nothing here mentions a measure. These are facts about the `PMF` layer as it
stands, and they are what `Causal.measureMinimaxRisk` is compared against.
-/

namespace AISafetyAtlas.Causal

variable {C : Type*} [Fintype C] [DecidableEq C] {dim : C → ℕ}

/-! ## Rounding a real down to a grid -/

/-- The largest multiple of `ε` not exceeding `x`. -/
@[expose] public noncomputable def floorMul (ε x : ℝ) : ℝ := ⌊x / ε⌋ * ε

public theorem floorMul_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : floorMul ε x ≤ x := by
  have h : (⌊x / ε⌋ : ℝ) ≤ x / ε := Int.floor_le _
  calc floorMul ε x = (⌊x / ε⌋ : ℝ) * ε := rfl
    _ ≤ (x / ε) * ε := by exact mul_le_mul_of_nonneg_right h hε.le
    _ = x := by field_simp

public theorem sub_floorMul_lt {ε : ℝ} (hε : 0 < ε) (x : ℝ) : x - floorMul ε x < ε := by
  have h : x / ε - 1 < (⌊x / ε⌋ : ℝ) := by
    have := Int.sub_one_lt_floor (x / ε)
    linarith
  have h' : (x / ε - 1) * ε < (⌊x / ε⌋ : ℝ) * ε := by
    exact mul_lt_mul_of_pos_right h hε
  have hx : (x / ε) * ε = x := by field_simp
  simp only [floorMul]
  nlinarith [h', hx]

public theorem floorMul_nonneg {ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) :
    0 ≤ floorMul ε x := by
  have h : (0 : ℤ) ≤ ⌊x / ε⌋ := Int.floor_nonneg.mpr (div_nonneg hx hε.le)
  have : (0 : ℝ) ≤ (⌊x / ε⌋ : ℝ) := by exact_mod_cast h
  exact mul_nonneg this hε.le

/-! ## The last table index

A conditional table over `Fin n` is rounded by rounding every index except the
last one down, and giving the last whatever mass remains. -/

private theorem filter_last_eq {n : ℕ} (a : Fin n) (ha : (a : ℕ) + 1 = n) :
    Finset.univ.filter (fun b : Fin n ↦ (b : ℕ) + 1 = n) = {a} := by
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hb
    exact Fin.ext (by omega)
  · rintro rfl
    exact ha

private theorem sum_notLast {n : ℕ} (a : Fin n) (ha : (a : ℕ) + 1 = n) (x : Fin n → ℝ)
    (hsum : ∑ b, x b = 1) :
    ∑ b ∈ Finset.univ.filter (fun b : Fin n ↦ ¬ ((b : ℕ) + 1 = n)), x b = 1 - x a := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    Finset.univ (fun b : Fin n ↦ (b : ℕ) + 1 = n) x
  rw [filter_last_eq a ha, Finset.sum_singleton, hsum] at hsplit
  linarith

/-! ## Rounding a model -/

/-- The model obtained by rounding every table entry **down** to a multiple of
`ε`, except the last entry of each conditional, which absorbs the remainder.

The graph, the acyclicity witness and the dimensions are untouched: only the
tables move. Rounding down is what preserves the simplex — it can only free
mass, so the remainder given to the last entry stays non-negative. -/
@[expose] public noncomputable def Model.roundDown (M : Model C dim ℝ) {ε : ℝ}
    (hε : 0 < ε) : Model C dim ℝ where
  dim_pos := M.dim_pos
  parents := M.parents
  acyclic := M.acyclic
  cpt := fun c a v ↦
    if (a : ℕ) + 1 = dim c then
      1 - ∑ b ∈ Finset.univ.filter (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c)),
            floorMul ε (M.cpt c b v)
    else floorMul ε (M.cpt c a v)
  cpt_parents := fun c a v w h ↦ by
    have hcpt : ∀ b : Fin (dim c), M.cpt c b v = M.cpt c b w := fun b ↦
      M.cpt_parents c b v w h
    by_cases ha : (a : ℕ) + 1 = dim c
    · simp only [if_pos ha]
      have : ∀ b ∈ Finset.univ.filter (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c)),
          floorMul ε (M.cpt c b v) = floorMul ε (M.cpt c b w) := by
        intro b _
        rw [hcpt b]
      rw [Finset.sum_congr rfl this]
    · simp only [if_neg ha, hcpt a]
  cpt_nonneg := fun c a v ↦ by
    by_cases ha : (a : ℕ) + 1 = dim c
    · simp only [if_pos ha]
      have hle : ∑ b ∈ Finset.univ.filter (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c)),
          floorMul ε (M.cpt c b v)
          ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c)),
              M.cpt c b v :=
        Finset.sum_le_sum fun b _ ↦ floorMul_le hε _
      rw [sum_notLast a ha _ (M.cpt_sum c v)] at hle
      have := M.cpt_nonneg c a v
      linarith
    · simp only [if_neg ha]
      exact floorMul_nonneg hε (M.cpt_nonneg c a v)
  cpt_sum := fun c v ↦ by
    classical
    have hpos := M.dim_pos c
    set a : Fin (dim c) := ⟨dim c - 1, by omega⟩ with ha_def
    have ha : (a : ℕ) + 1 = dim c := by simp [ha_def]; omega
    have hsplit := Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun b : Fin (dim c) ↦ (b : ℕ) + 1 = dim c)
      (fun b ↦ if (b : ℕ) + 1 = dim c then
        1 - ∑ b' ∈ Finset.univ.filter (fun b' : Fin (dim c) ↦ ¬ ((b' : ℕ) + 1 = dim c)),
              floorMul ε (M.cpt c b' v)
      else floorMul ε (M.cpt c b v))
    rw [filter_last_eq a ha, Finset.sum_singleton, if_pos ha] at hsplit
    have hrest : ∑ b ∈ Finset.univ.filter (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c)),
        (if (b : ℕ) + 1 = dim c then
          1 - ∑ b' ∈ Finset.univ.filter (fun b' : Fin (dim c) ↦ ¬ ((b' : ℕ) + 1 = dim c)),
                floorMul ε (M.cpt c b' v)
        else floorMul ε (M.cpt c b v))
        = ∑ b ∈ Finset.univ.filter (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c)),
            floorMul ε (M.cpt c b v) := by
      refine Finset.sum_congr rfl fun b hb ↦ ?_
      rw [Finset.mem_filter] at hb
      rw [if_neg hb.2]
    rw [hrest] at hsplit
    rw [← hsplit]
    ring

@[simp] public theorem Model.parents_roundDown (M : Model C dim ℝ) {ε : ℝ} (hε : 0 < ε) :
    (M.roundDown hε).parents = M.parents := rfl

/-- Every table entry moves by at most `dim c · ε`. The bound is `dim c · ε` and
not `ε` because the last entry absorbs the rounding error of all the others. -/
public theorem Model.abs_cpt_roundDown_sub (M : Model C dim ℝ) {ε : ℝ} (hε : 0 < ε)
    (c : C) (a : Fin (dim c)) (v : Assignment C dim) :
    |(M.roundDown hε).cpt c a v - M.cpt c a v| ≤ (dim c : ℝ) * ε := by
  classical
  have hpos := M.dim_pos c
  have hone : (1 : ℝ) ≤ (dim c : ℝ) := by exact_mod_cast hpos
  by_cases ha : (a : ℕ) + 1 = dim c
  · have hval : (M.roundDown hε).cpt c a v
        = 1 - ∑ b ∈ Finset.univ.filter (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c)),
              floorMul ε (M.cpt c b v) := by
      simp only [Model.roundDown, if_pos ha]
    have hrem := sum_notLast a ha (fun b ↦ M.cpt c b v) (M.cpt_sum c v)
    have hgap : (M.roundDown hε).cpt c a v - M.cpt c a v
        = ∑ b ∈ Finset.univ.filter (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c)),
            (M.cpt c b v - floorMul ε (M.cpt c b v)) := by
      rw [hval, Finset.sum_sub_distrib, hrem]
      ring
    have hlo : 0 ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c)),
        (M.cpt c b v - floorMul ε (M.cpt c b v)) :=
      Finset.sum_nonneg fun b _ ↦ by linarith [floorMul_le hε (M.cpt c b v)]
    have hhi : ∑ b ∈ Finset.univ.filter (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c)),
        (M.cpt c b v - floorMul ε (M.cpt c b v)) ≤ (dim c : ℝ) * ε := by
      refine le_trans (Finset.sum_le_card_nsmul _ _ ε fun b _ ↦
        (sub_floorMul_lt hε (M.cpt c b v)).le) ?_
      have hcard : ((Finset.univ.filter
          (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c))).card : ℝ) ≤ (dim c : ℝ) := by
        have := Finset.card_filter_le (Finset.univ : Finset (Fin (dim c)))
          (fun b : Fin (dim c) ↦ ¬ ((b : ℕ) + 1 = dim c))
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this
      simp only [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard hε.le
    rw [hgap, abs_of_nonneg hlo]
    exact hhi
  · have hval : (M.roundDown hε).cpt c a v = floorMul ε (M.cpt c a v) := by
      simp only [Model.roundDown, if_neg ha]
    rw [hval, abs_sub_comm, abs_of_nonneg (by linarith [floorMul_le hε (M.cpt c a v)])]
    have := sub_floorMul_lt hε (M.cpt c a v)
    nlinarith

/-! ## The error moves by `O(ε)`

`modelError` is a nested `Finset.sup'` of absolute differences, and a supremum
is `1`-Lipschitz in its argument. -/

private theorem abs_sup'_sub_sup'_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f g : ι → ℝ) (r : ℝ) (h : ∀ i ∈ s, |f i - g i| ≤ r) :
    |s.sup' hs f - s.sup' hs g| ≤ r := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    refine Finset.sup'_le _ _ fun i hi ↦ ?_
    have h1 : f i - g i ≤ r := (abs_le.mp (h i hi)).2
    have h2 : g i ≤ s.sup' hs g := Finset.le_sup' g hi
    linarith
  · rw [sub_le_iff_le_add]
    refine Finset.sup'_le _ _ fun i hi ↦ ?_
    have h1 : g i - f i ≤ r := by
      have := (abs_le.mp (h i hi)).1
      linarith
    have h2 : f i ≤ s.sup' hs f := Finset.le_sup' f hi
    linarith

/-- Rounding the estimate moves the printed error by at most `n · ε`, for any
`n` bounding the variable dimensions.

This is the whole mathematical content of the countable-support repair: the
error is `1`-Lipschitz in the estimate, so a rounded estimate is almost as good,
and rounded estimates range over a countable set. -/
public theorem modelError_roundDown_le [Nonempty C] (M M' : Model C dim ℝ) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) (hn : ∀ c, dim c ≤ n) :
    |modelError M (M'.roundDown hε) - modelError M M'| ≤ (n : ℝ) * ε := by
  classical
  have hn0 : (0 : ℝ) ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε.le
  have hpar : (M'.roundDown hε).parents = M'.parents := rfl
  by_cases hp : M.parents = M'.parents
  · have hp' : M.parents = (M'.roundDown hε).parents := by rw [hpar, hp]
    simp only [modelError, if_pos hp, if_pos hp']
    refine abs_sup'_sub_sup'_le _ _ _ _ fun c _ ↦ ?_
    refine abs_sup'_sub_sup'_le _ _ _ _ fun av _ ↦ ?_
    have hstep : |M.cpt c av.1 av.2 - (M'.roundDown hε).cpt c av.1 av.2|
        - |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|
        ≤ |(M'.roundDown hε).cpt c av.1 av.2 - M'.cpt c av.1 av.2| := by
      have := abs_sub_abs_le_abs_sub (M.cpt c av.1 av.2 - (M'.roundDown hε).cpt c av.1 av.2)
        (M.cpt c av.1 av.2 - M'.cpt c av.1 av.2)
      calc |M.cpt c av.1 av.2 - (M'.roundDown hε).cpt c av.1 av.2|
            - |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|
          ≤ |(M.cpt c av.1 av.2 - (M'.roundDown hε).cpt c av.1 av.2)
              - (M.cpt c av.1 av.2 - M'.cpt c av.1 av.2)| := this
        _ = |M'.cpt c av.1 av.2 - (M'.roundDown hε).cpt c av.1 av.2| := by ring_nf
        _ = |(M'.roundDown hε).cpt c av.1 av.2 - M'.cpt c av.1 av.2| := abs_sub_comm _ _
    have hstep' : |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|
        - |M.cpt c av.1 av.2 - (M'.roundDown hε).cpt c av.1 av.2|
        ≤ |(M'.roundDown hε).cpt c av.1 av.2 - M'.cpt c av.1 av.2| := by
      have := abs_sub_abs_le_abs_sub (M.cpt c av.1 av.2 - M'.cpt c av.1 av.2)
        (M.cpt c av.1 av.2 - (M'.roundDown hε).cpt c av.1 av.2)
      calc |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|
            - |M.cpt c av.1 av.2 - (M'.roundDown hε).cpt c av.1 av.2|
          ≤ |(M.cpt c av.1 av.2 - M'.cpt c av.1 av.2)
              - (M.cpt c av.1 av.2 - (M'.roundDown hε).cpt c av.1 av.2)| := this
        _ = |(M'.roundDown hε).cpt c av.1 av.2 - M'.cpt c av.1 av.2| := by ring_nf
    have hbound : |(M'.roundDown hε).cpt c av.1 av.2 - M'.cpt c av.1 av.2| ≤ (n : ℝ) * ε := by
      refine le_trans (M'.abs_cpt_roundDown_sub hε c av.1 av.2) ?_
      have : ((dim c : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn c
      exact mul_le_mul_of_nonneg_right this hε.le
    rw [abs_le]
    constructor <;> [linarith; linarith]
  · have hp' : ¬ M.parents = (M'.roundDown hε).parents := by rw [hpar]; exact hp
    simp only [modelError, if_neg hp, if_neg hp']
    simpa using hn0

/-! ## The model space as a measurable space

A model is a graph together with an array of real table entries. The graph
ranges over a finite type and carries no structure worth respecting, so it
contributes the discrete σ-algebra; the entries are real coordinates and
contribute the product Borel one.

This is the weakest structure making every table entry measurable and every
graph fibre measurable, which is exactly what the printed error reads. -/

public instance instMeasurableSpaceModel : MeasurableSpace (Model C dim ℝ) :=
  MeasurableSpace.comap (fun M : Model C dim ℝ ↦ M.cpt) inferInstance ⊔
    MeasurableSpace.comap (fun M : Model C dim ℝ ↦ M.parents) ⊤

/-- Every table entry is a measurable coordinate. -/
public theorem measurable_cpt (c : C) (a : Fin (dim c)) (v : Assignment C dim) :
    Measurable fun M : Model C dim ℝ ↦ M.cpt c a v := by
  have hcomap : @Measurable _ _ (MeasurableSpace.comap (fun M : Model C dim ℝ ↦ M.cpt)
      inferInstance) _ (fun M : Model C dim ℝ ↦ M.cpt) :=
    Measurable.of_comap_le le_rfl
  have h1 := (measurable_pi_apply c).comp hcomap
  have h2 := (measurable_pi_apply a).comp h1
  have h3 := (measurable_pi_apply v).comp h2
  exact h3.mono le_sup_left le_rfl

/-- Every graph fibre is measurable. -/
public theorem measurableSet_parents_eq (G : C → Finset C) :
    MeasurableSet {M : Model C dim ℝ | M.parents = G} := by
  have hs : @MeasurableSet _
      (MeasurableSpace.comap (fun M : Model C dim ℝ ↦ M.parents) ⊤)
      {M : Model C dim ℝ | M.parents = G} :=
    ⟨{G}, trivial, by ext M; simp⟩
  exact (le_sup_right : _ ≤ instMeasurableSpaceModel) _ hs

/-- Singletons are measurable: a model is pinned down by its graph together with
its finitely many table entries, and each of those is a measurable condition. -/
public instance instMeasurableSingletonClassModel :
    MeasurableSingletonClass (Model C dim ℝ) where
  measurableSet_singleton M := by
    have hset : ({M} : Set (Model C dim ℝ))
        = {M' : Model C dim ℝ | M'.parents = M.parents} ∩
            ⋂ c : C, ⋂ a : Fin (dim c), ⋂ v : Assignment C dim,
              {M' : Model C dim ℝ | M'.cpt c a v = M.cpt c a v} := by
      ext M'
      simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_setOf_eq]
      constructor
      · rintro rfl
        exact ⟨rfl, fun _ _ _ ↦ rfl⟩
      · rintro ⟨hp, hc⟩
        exact Model.ext hp (funext fun c ↦ funext fun a ↦ funext fun v ↦ hc c a v)
    rw [hset]
    refine (measurableSet_parents_eq _).inter ?_
    refine MeasurableSet.iInter fun c ↦ MeasurableSet.iInter fun a ↦
      MeasurableSet.iInter fun v ↦ ?_
    exact measurable_cpt c a v (measurableSet_singleton (M.cpt c a v))

/-! ## Rounded models form a countable set

A rounded table entry is determined by an integer — which multiple of `ε` it
is — and there are finitely many entries and finitely many graphs. So the
rounded models are indexed by a countable type, which is exactly what a `PMF`
can be supported on. -/

/-- The integer data a rounded model is determined by. -/
@[expose] public noncomputable def Model.roundKey (M : Model C dim ℝ) (ε : ℝ) :
    (C → Finset C) × ((c : C) → Fin (dim c) → Assignment C dim → ℤ) :=
  (M.parents, fun c a v ↦ ⌊M.cpt c a v / ε⌋)

/-- Two models with the same integer data round to the same model. -/
public theorem Model.roundDown_eq_of_roundKey_eq {M M' : Model C dim ℝ} {ε : ℝ}
    (hε : 0 < ε) (h : M.roundKey ε = M'.roundKey ε) :
    M.roundDown hε = M'.roundDown hε := by
  classical
  obtain ⟨hpar, hfl⟩ := Prod.mk.injEq .. ▸ h
  have hfloor : ∀ c a v, floorMul ε (M.cpt c a v) = floorMul ε (M'.cpt c a v) := by
    intro c a v
    have := congrFun (congrFun (congrFun hfl c) a) v
    simp only [floorMul, this]
  refine Model.ext hpar (funext fun c ↦ funext fun a ↦ funext fun v ↦ ?_)
  by_cases ha : (a : ℕ) + 1 = dim c
  · simp only [Model.roundDown, if_pos ha]
    exact congrArg _ (Finset.sum_congr rfl fun b _ ↦ hfloor c b v)
  · simp only [Model.roundDown, if_neg ha]
    exact hfloor c a v

/-- **The rounded models are countable.** A `PMF` can be supported on them, which
is what makes the rounding a repair for the output-law restriction rather than
merely an approximation. -/
public theorem countable_range_roundDown {ε : ℝ} (hε : 0 < ε) :
    Set.Countable (Set.range fun M : Model C dim ℝ ↦ M.roundDown hε) := by
  classical
  rcases isEmpty_or_nonempty (Model C dim ℝ) with hE | hN
  · rw [Set.range_eq_empty]
    exact Set.countable_empty
  · refine Set.Countable.mono ?_ (Set.countable_range
      fun d ↦ (Function.invFun (fun M : Model C dim ℝ ↦ M.roundKey ε) d).roundDown hε)
    rintro _ ⟨M, rfl⟩
    refine ⟨M.roundKey ε, ?_⟩
    have hinv := Function.invFun_eq
      (f := fun M : Model C dim ℝ ↦ M.roundKey ε) ⟨M, rfl⟩
    exact Model.roundDown_eq_of_roundKey_eq hε hinv

/-! ## The printed error is measurable

`modelError` is a nested `Finset.sup'` of coordinate differences on the graph
fibre, and `1` off it. Both pieces are measurable, and the fibre is. -/

public theorem measurable_modelError [Nonempty C] (M : Model C dim ℝ) :
    Measurable fun M' : Model C dim ℝ ↦ modelError M M' := by
  classical
  have hentry : ∀ (c : C) (av : Fin (dim c) × Assignment C dim),
      Measurable fun M' : Model C dim ℝ ↦ |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2| :=
    fun c av ↦ Measurable.abs (measurable_const.sub (measurable_cpt c av.1 av.2))
  have hc : ∀ c : C, Measurable fun M' : Model C dim ℝ ↦ cptError M M' c := by
    intro c
    have hne : (Finset.univ : Finset (Fin (dim c) × Assignment C dim)).Nonempty :=
      ⟨(⟨0, M.dim_pos c⟩, fun i ↦ ⟨0, M.dim_pos i⟩), Finset.mem_univ _⟩
    have heq : (fun M' : Model C dim ℝ ↦ cptError M M' c)
        = Finset.sup' Finset.univ hne
            (fun av : Fin (dim c) × Assignment C dim ↦ fun M' : Model C dim ℝ ↦
              |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|) := by
      funext M'
      rw [Finset.sup'_apply]
      rfl
    rw [heq]
    exact Finset.measurable_sup' hne fun av _ ↦ hentry c av
  have hsup : Measurable fun M' : Model C dim ℝ ↦
      Finset.sup' (Finset.univ : Finset C) Finset.univ_nonempty (cptError M M') := by
    have heq : (fun M' : Model C dim ℝ ↦
        Finset.sup' (Finset.univ : Finset C) Finset.univ_nonempty (cptError M M'))
        = Finset.sup' Finset.univ Finset.univ_nonempty
            (fun c : C ↦ fun M' : Model C dim ℝ ↦ cptError M M' c) := by
      funext M'
      rw [Finset.sup'_apply]
    rw [heq]
    exact Finset.measurable_sup' _ fun c _ ↦ hc c
  have hpiece : ∀ M' : Model C dim ℝ, modelError M M'
      = if M'.parents = M.parents
        then Finset.sup' (Finset.univ : Finset C) Finset.univ_nonempty (cptError M M')
        else 1 := by
    intro M'
    unfold modelError
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  rw [funext hpiece]
  exact Measurable.ite (measurableSet_parents_eq _) hsup measurable_const

/-! ## The rounding map is measurable

The rounded model is determined by the **key** — the graph together with the
integers each entry floors to — and the key ranges over a countable type. So the
rounding map factors through a countable set, and measurability reduces to the
key fibres, each of which is a finite intersection of level sets of measurable
coordinates. No measurability lemma for `Int.floor` is needed: the floor is
never measured, only its level sets, and `Int.floor_eq_iff` turns those into
half-open intervals. -/

private theorem measurableSet_floor_eq {ε : ℝ} (c : C) (a : Fin (dim c))
    (v : Assignment C dim) (n : ℤ) :
    MeasurableSet {M : Model C dim ℝ | ⌊M.cpt c a v / ε⌋ = n} := by
  have heq : {M : Model C dim ℝ | ⌊M.cpt c a v / ε⌋ = n}
      = (fun M : Model C dim ℝ ↦ M.cpt c a v / ε) ⁻¹' Set.Ico (n : ℝ) (n + 1) := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ico]
    exact Int.floor_eq_iff
  rw [heq]
  exact ((measurable_cpt c a v).div_const ε) measurableSet_Ico

private theorem measurableSet_roundKey_eq {ε : ℝ}
    (k : (C → Finset C) × ((c : C) → Fin (dim c) → Assignment C dim → ℤ)) :
    MeasurableSet {M : Model C dim ℝ | M.roundKey ε = k} := by
  have heq : {M : Model C dim ℝ | M.roundKey ε = k}
      = {M : Model C dim ℝ | M.parents = k.1} ∩
          ⋂ c : C, ⋂ a : Fin (dim c), ⋂ v : Assignment C dim,
            {M : Model C dim ℝ | ⌊M.cpt c a v / ε⌋ = k.2 c a v} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Model.roundKey,
      Prod.ext_iff]
    constructor
    · rintro ⟨hp, hf⟩
      exact ⟨hp, fun c a v ↦ congrFun (congrFun (congrFun hf c) a) v⟩
    · rintro ⟨hp, hf⟩
      exact ⟨hp, funext fun c ↦ funext fun a ↦ funext fun v ↦ hf c a v⟩
  rw [heq]
  refine (measurableSet_parents_eq _).inter ?_
  exact MeasurableSet.iInter fun c ↦ MeasurableSet.iInter fun a ↦
    MeasurableSet.iInter fun v ↦ measurableSet_floor_eq c a v _

/-- **The rounding map is measurable**, which is what lets an output measure be
pushed onto the countable set of rounded models. -/
public theorem measurable_roundDown {ε : ℝ} (hε : 0 < ε) :
    Measurable fun M : Model C dim ℝ ↦ M.roundDown hε := by
  classical
  rcases isEmpty_or_nonempty (Model C dim ℝ) with hE | hN
  · exact fun s _ ↦ Subsingleton.measurableSet
  · letI : MeasurableSpace ((C → Finset C) ×
      ((c : C) → Fin (dim c) → Assignment C dim → ℤ)) := ⊤
    have hkey : Measurable fun M : Model C dim ℝ ↦ M.roundKey ε := by
      intro t _
      have heq : (fun M : Model C dim ℝ ↦ M.roundKey ε) ⁻¹' t
          = ⋃ k ∈ t, {M : Model C dim ℝ | M.roundKey ε = k} := by
        ext M
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
        exact ⟨fun h ↦ ⟨_, h, rfl⟩, fun ⟨k, hk, hkey⟩ ↦ hkey ▸ hk⟩
      rw [heq]
      exact MeasurableSet.biUnion t.to_countable fun k _ ↦ measurableSet_roundKey_eq k
    have hfac : (fun M : Model C dim ℝ ↦ M.roundDown hε)
        = (fun k ↦ (Function.invFun (fun M : Model C dim ℝ ↦ M.roundKey ε) k).roundDown hε)
          ∘ fun M : Model C dim ℝ ↦ M.roundKey ε := by
      funext M
      have hinv := Function.invFun_eq
        (f := fun M : Model C dim ℝ ↦ M.roundKey ε) ⟨M, rfl⟩
      exact (Model.roundDown_eq_of_roundKey_eq hε hinv).symm
    rw [hfac]
    have hg : @Measurable _ _ ⊤ _
        (fun k ↦ (Function.invFun
          (fun M : Model C dim ℝ ↦ M.roundKey ε) k).roundDown hε) := fun _ _ ↦ trivial
    exact hg.comp hkey

end AISafetyAtlas.Causal
