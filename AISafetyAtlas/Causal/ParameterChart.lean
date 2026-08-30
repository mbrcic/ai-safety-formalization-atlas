module

public import AISafetyAtlas.Causal.MarginClass
public import AISafetyAtlas.Analysis.Semialgebraic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The free-coordinate chart of a binary causal model

MAIS-A2 `def:margin` closes with *"Write `K(G) = Σᵢ 2^{|Pa_G(Cᵢ)|}` for the
number of free table entries"*, and `prob:effective` (MAIS-O24) is stated over
those coordinates: a list of rational polynomials **in `(θ, u)`**, with a
Lebesgue estimate on the `θ` at which a polynomial is small. Neither can be
written down without an object called `θ`.

This module supplies it. A model on a fixed graph `G` over binary chance
variables is `K(G)` real numbers — one per variable per parent configuration,
the probability that the variable is `1` — and nothing else.
`Model.chartOn` reads them off, `Model.ofChart` puts them back, and
`Model.chartOn_ofChart` / `Model.ofChart_chartOn` make the pair a bijection onto
the models carrying `G`.

Both directions are needed and neither is decorative. MAIS-O24's conclusion (c)
integrates over `θ` with no model in sight, while (a) and (b) cut out a subclass
of *models* by a condition on their `θ`. Those are the same condition only
because every point of the box is realized by a model, which is
`Model.ofChart`. Acyclicity is the one thing a chart point does not carry, so it
enters as a hypothesis on `G`.

**Scope.** `K` and the coordinate count are printed, so they are held to the
source's own definition rather than to a convenient one:
`card_chartIndex` proves `Fintype.card (ChartIndex G) = Σᵢ 2^{|Pa_G(Cᵢ)|}`
against `def:margin`'s formula. The chart is stated for binary chance
variables because `def:cid` declares them binary; a variable of dimension `d`
would contribute `(d-1)·2^{|Pa|}` free entries and `def:margin`'s `K(G)` would
not be the printed formula.

The measure is the Lebesgue measure `MeasureTheory.volume` on
`ChartIndex G → ℝ`, which is what `prob:effective`(c)'s
`Leb{θ : |Q^G_j(θ,u)| < μ}` quantifies over. Nothing here states (a), (b) or
(c); this is the coordinate layer they are phrased in.
-/

namespace AISafetyAtlas.Causal

open MeasureTheory
open AISafetyAtlas.Analysis

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- A parent configuration of `c` under the graph `G`: an assignment of a bit to
each declared parent, and nothing else. -/
public abbrev ParentConfig (G : C → Finset C) (c : C) := G c → Fin 2

/-- The index set of MAIS-A2's free table coordinates `θ`: one coordinate per
chance variable per parent configuration. -/
public abbrev ChartIndex (G : C → Finset C) := (c : C) × ParentConfig G c

/-- `K(G)`, the number of free table entries, as `def:margin` writes it. -/
@[expose] public noncomputable def chartDim (G : C → Finset C) : ℕ :=
  ∑ c : C, 2 ^ (G c).card

/-- The chart has exactly `K(G)` coordinates. This is the printed formula, not a
convenient recount of it. -/
public theorem card_chartIndex (G : C → Finset C) :
    Fintype.card (ChartIndex G) = chartDim G := by
  classical
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp [ParentConfig]

omit [Fintype C] [DecidableEq C] in
/-- A binary chance variable takes one of two values. Stated at
`Fin (binaryDim C c)` rather than `Fin 2` so that it applies directly to a
`Model`'s table index without unfolding `binaryDim` at the call site. -/
public theorem binary_eq_zero_or_one {c : C} (a : Fin (binaryDim C c)) :
    a = 0 ∨ a = 1 := by
  have h := a.isLt
  interval_cases h2 : (a : ℕ) <;> [left; right] <;> exact Fin.ext h2

/-- The full assignment a parent configuration names, padding the non-parents
with `0`. Which padding is used never matters, by `cpt_parents`. -/
@[expose] public def ChartIndex.extend {G : C → Finset C} (i : ChartIndex G) :
    Assignment C (binaryDim C) :=
  fun c ↦ if hc : c ∈ G i.1 then i.2 ⟨c, hc⟩ else 0

/-- Read a model's free coordinates **at a named graph**: for each variable and
parent configuration of `G`, the probability that the variable takes the value
`1`. The remaining table cell is `1 -` this one, by `cpt_sum`, which is why
these are the *free* entries and why there are `K(G)` of them and not `2·K(G)`.

`G` is a parameter rather than `M.parents` because MAIS-O24's three conclusions
do not agree on which one is fixed: (c) fixes `G` and integrates over `θ`, while
(a) and (b) range over models and read *their* graph's `θ`. Indexing everything
by one free `G` is what lets the two be stated side by side. The reading is only
meaningful when `M.parents = G`, and every statement below that uses it carries
that hypothesis. -/
@[expose] public noncomputable def Model.chartOn (M : Model C (binaryDim C) ℝ)
    (G : C → Finset C) : ChartIndex G → ℝ :=
  fun i ↦ M.cpt i.1 1 i.extend

/-- The chart at a model's own graph. -/
public noncomputable abbrev Model.chart (M : Model C (binaryDim C) ℝ) :
    ChartIndex M.parents → ℝ :=
  M.chartOn M.parents

/-- The coordinate does not depend on how the parent configuration is extended
to a full assignment — which is `cpt_parents`, read in coordinates. -/
public theorem Model.chartOn_apply (M : Model C (binaryDim C) ℝ)
    {G : C → Finset C} (hG : M.parents = G) (i : ChartIndex G)
    (v : Assignment C (binaryDim C)) (hv : ∀ p : G i.1, v p.1 = i.2 p) :
    M.chartOn G i = M.cpt i.1 1 v := by
  refine M.cpt_parents i.1 1 _ v fun p hp ↦ ?_
  rw [hG] at hp
  simpa [ChartIndex.extend, hp] using (hv ⟨p, hp⟩).symm

/-- Every chart coordinate is a probability. -/
public theorem Model.chartOn_mem_unitInterval (M : Model C (binaryDim C) ℝ)
    (G : C → Finset C) (i : ChartIndex G) :
    0 ≤ M.chartOn G i ∧ M.chartOn G i ≤ 1 := by
  refine ⟨M.cpt_nonneg _ _ _, ?_⟩
  have hsum := M.cpt_sum i.1 i.extend
  have hzero := M.cpt_nonneg i.1 0 i.extend
  rw [Fin.sum_univ_two] at hsum
  unfold Model.chartOn
  linarith

/-- **A chart point is a model.** Given a graph with a topological order and a
point of the unit box, rebuild the binary model whose free coordinates it is.

This is the direction MAIS-O24 needs and `chartOn` does not supply: conclusion
(c) integrates over `θ` with no model in sight, while (a) reads a subclass of
*models*, and the two are the same condition only if every chart point is
realized. Acyclicity is the one thing a chart point does not carry, so it comes
in as a hypothesis on `G`. -/
@[expose] public noncomputable def Model.ofChart (G : C → Finset C)
    (hacyclic : ∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c)
    (θ : ChartIndex G → ℝ) (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) :
    Model C (binaryDim C) ℝ where
  dim_pos := fun _ ↦ by norm_num
  parents := G
  acyclic := hacyclic
  cpt := fun c a v ↦
    if a = 1 then θ ⟨c, fun p ↦ v p.1⟩ else 1 - θ ⟨c, fun p ↦ v p.1⟩
  cpt_parents := fun c a v w h ↦ by
    have : (fun p : G c ↦ v p.1) = (fun p : G c ↦ w p.1) := funext fun p ↦ h p.1 p.2
    rw [this]
  cpt_nonneg := fun c a v ↦ by
    rcases (hθ ⟨c, fun p ↦ v p.1⟩) with ⟨h0, h1⟩
    by_cases ha : a = 1 <;> simp [ha] <;> linarith
  cpt_sum := fun c v ↦ by
    rw [Fin.sum_univ_two]
    norm_num

@[simp] public theorem Model.parents_ofChart (G : C → Finset C)
    (hacyclic : ∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c)
    (θ : ChartIndex G → ℝ) (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) :
    (Model.ofChart G hacyclic θ hθ).parents = G := by
  simp [Model.ofChart]

/-- Rebuilding from a point and reading it back is the identity. -/
public theorem Model.chartOn_ofChart (G : C → Finset C)
    (hacyclic : ∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c)
    (θ : ChartIndex G → ℝ) (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) :
    (Model.ofChart G hacyclic θ hθ).chartOn G = θ := by
  funext i
  have hcfg : (fun p : G i.1 ↦ i.extend p.1) = i.2 := by
    funext p
    simp [ChartIndex.extend, p.2]
  simp [Model.chartOn, Model.ofChart, hcfg]

/-- Reading a model's point and rebuilding is the identity. Together with
`chartOn_ofChart` this makes the chart a bijection onto the models carrying `G`,
which is what lets a Lebesgue statement about `θ` be a statement about models. -/
public theorem Model.ofChart_chartOn (M : Model C (binaryDim C) ℝ)
    {G : C → Finset C} (hG : M.parents = G) :
    Model.ofChart G (hG ▸ M.acyclic) (M.chartOn G)
      (M.chartOn_mem_unitInterval G) = M := by
  refine Model.ext (by simp [hG]) (funext fun c ↦ funext fun a ↦ funext fun v ↦ ?_)
  have hread : M.chartOn G ⟨c, fun p : G c ↦ v p.1⟩ = M.cpt c 1 v :=
    M.chartOn_apply hG _ v fun _ ↦ rfl
  have hsum := M.cpt_sum c v
  rw [Fin.sum_univ_two] at hsum
  simp only [Model.ofChart]
  rcases binary_eq_zero_or_one a with rfl | rfl
  · rw [if_neg (by simp), hread]; linarith
  · rw [if_pos rfl, hread]

/-! ## The geometry `prob:exact` quantifies over

MAIS-O25 opens *"Let `𝒩 ⊆ 𝕄(sk, λ)` be a **compact semialgebraic** class
satisfying conclusions (a)–(b) of Problem `prob:effective` with modulus
`ω(δ) = Lδ`. Assume also a richness condition: for some graph `G` and `ρ > 0`,
its **table-parameter projection** contains a `K(G)`-dimensional box of side
`ρ`."*

Both conditions are about the *projection* of a class into `θ`-space, not about
the class as an abstract set of models, so both are stated through
`Model.chartOn`. That is what the chart was built for. -/

/-- The **table-parameter projection** of a model class at a fixed graph: the
set of chart points realized by members of the class carrying that graph.

A class generally spreads over several graphs, and `def:margin`'s `K(G)` depends
on the graph, so the projection is taken one graph at a time — the coordinate
spaces at different graphs are different spaces. -/
@[expose] public def Model.chartSlice
    (modelClass : Set (Model C (binaryDim C) ℝ)) (G : C → Finset C) :
    Set (ChartIndex G → ℝ) :=
  {θ | ∃ M ∈ modelClass, M.parents = G ∧ M.chartOn G = θ}

/-- **`prob:exact`'s "compact semialgebraic class"**, read on each graph's
coordinate space.

Neither word is decorative in the source. Compactness is what makes a supremum
of the error over the class attained rather than merely approached, and the
semialgebraic condition is what MAIS-O24's polynomial certificate is supposed to
supply — the two problems are linked through exactly this predicate. -/
@[expose] public def IsCompactSemialgebraicClass
    (modelClass : Set (Model C (binaryDim C) ℝ)) : Prop :=
  ∀ G : C → Finset C,
    IsCompact (Model.chartSlice modelClass G) ∧
      IsSemialgebraic (Model.chartSlice modelClass G)

/-- **`prob:exact`'s richness condition**: for some graph, the class's
table-parameter projection contains a full-dimensional closed box of side `ρ`.

The box is affine and literal — `ClosedBox corner rho` is `∏ᵢ [cᵢ, cᵢ + ρ]` over
all `K(G)` coordinates, which is what *"a `K(G)`-dimensional box of side `ρ`"*
says. The dimension is not a free parameter: it is forced to `K(G)` by the
coordinate space the box lives in, and `card_chartIndex` proves that count is the
printed `Σᵢ 2^{|Pa_G(Cᵢ)|}`. -/
@[expose] public def ContainsChartBox
    (modelClass : Set (Model C (binaryDim C) ℝ)) (rho : ℝ) : Prop :=
  0 < rho ∧ ∃ (G : C → Finset C) (corner : ChartIndex G → ℝ),
    ClosedBox corner rho ⊆ Model.chartSlice modelClass G

/-- A box witnessing richness is itself semialgebraic, so the richness condition
is compatible with the class condition rather than in tension with it: a class
can be cut out by polynomial sign conditions and still contain a solid box. -/
public theorem isSemialgebraic_of_containsChartBox
    {modelClass : Set (Model C (binaryDim C) ℝ)} {rho : ℝ}
    (h : ContainsChartBox modelClass rho) :
    ∃ (G : C → Finset C) (corner : ChartIndex G → ℝ),
      IsSemialgebraic (ClosedBox corner rho) ∧
        ClosedBox corner rho ⊆ Model.chartSlice modelClass G := by
  obtain ⟨-, G, corner, hsub⟩ := h
  exact ⟨G, corner, isSemialgebraic_closedBox corner rho, hsub⟩

end AISafetyAtlas.Causal
