module

public import AISafetyAtlas.SingularLearning.ChartAssembly
public import AISafetyAtlas.SingularLearning.ChartCoords
public import AISafetyAtlas.SingularLearning.DiffeoTransfer

/-!
# Carrying the pair through the elimination chart

Theorem 5.1 (`HasEliminationChartAt`) supplies an analytic diffeomorphism `Ψ : O ⟶ O'` between
open sets of `ParamSpace M N H` and `ChartSpace q p h n g`, sending the base point to the origin,
in which

    (1/12) · comparisonGerm (Ψ w) ≤ 2 K(w) ≤ 6 · comparisonGerm (Ψ w) .

`ChartGerm.lean` gives the pair of the comparison germ at the origin of the chart space in
Euclidean coordinates. This module joins the two: it conjugates `Ψ` into Euclidean coordinates
with `ChartCoords.lean`'s two continuous linear equivalences, transports the pair backwards along
it with print's Lemma 6.4(i) (`DiffeoTransfer.lean`), and then converts the two-sided comparison
into the pair of the loss itself with print's Lemma 6.2 (`PairTransfer.lean`).

`ChartTransport.lean` is a different module with a nearby name: it builds the reindexings out of
which `Ψ` itself is assembled. This one consumes the finished `Ψ` and moves a *pair* across it.

## The dimension bookkeeping

The parameter space is counted as `HN + MH` and the chart space as `q + (hn + ph) + g`. These
agree at a feasible stratum (`elim_dimension_split` in `EliminationChart.lean`) but only propositionally,
so the equality is a hypothesis here rather than a rewrite: the module is about the transport,
not about the count, and stating it this way keeps the arithmetic where it is proved.

## The constants

Print's `1/12` and `6` are for `2K`, and the germ transported is `K`. The two-sided constants
therefore come out as `1/24` and `3`; Lemma 6.2 does not care what they are, only that they are
positive and ordered, so no separate rescaling step is needed.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Filter Topology
open scoped Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- **Print's step 2, in Euclidean coordinates.** Given a chart at `(A*, B*)` and the pair of the
comparison germ at the origin of the chart space, the loss has that same pair at the Euclidean
coordinates of `(A*, B*)`. -/
public theorem hasLocalVolumeOrder_rrrLoss_coords
    {M N H q p h n g : ℕ} (hdim : H * N + M * H = q + (h * n + p * h) + g)
    {C : Matrix (Fin M) (Fin N) ℝ} {Astar : Matrix (Fin H) (Fin N) ℝ}
    {Bstar : Matrix (Fin M) (Fin H) ℝ}
    (hchart : HasEliminationChartAt C Astar Bstar q p h n g)
    {lam : ℝ} {m : ℕ} (hpair : HasLocalVolumeOrder (chartGerm q p h n g) 0 lam m) :
    HasLocalVolumeOrder
      (fun x => rrrLoss C ((matrixPairEquiv M N H).symm x).1 ((matrixPairEquiv M N H).symm x).2)
      (matrixPairCoords Astar Bstar) lam m := by
  classical
  obtain ⟨O, O', Ψ, Φ, hO, hO', hbase, hbij, hinvOn, hΨ, hΦ, hΨ0, hcomp⟩ := hchart
  set pc := paramCoords M N H with hpc
  set cc := chartCoords q p h n g with hcc
  -- the two open sets, in coordinates
  set U : Set (EuclideanSpace ℝ (Fin (H * N + M * H))) := pc '' O with hU
  set V : Set (EuclideanSpace ℝ (Fin (q + (h * n + p * h) + g))) := cc '' O' with hV
  have hUopen : IsOpen U := pc.toHomeomorph.isOpenMap O hO
  have hVopen : IsOpen V := cc.toHomeomorph.isOpenMap O' hO'
  set w₀ : EuclideanSpace ℝ (Fin (H * N + M * H)) := matrixPairCoords Astar Bstar with hw₀
  have hw₀U : w₀ ∈ U := ⟨(Astar, Bstar), hbase, rfl⟩
  -- the conjugated chart
  set φ : EuclideanSpace ℝ (Fin (H * N + M * H)) →
      EuclideanSpace ℝ (Fin (q + (h * n + p * h) + g)) := fun x => cc (Ψ (pc.symm x)) with hφ
  set ψ : EuclideanSpace ℝ (Fin (q + (h * n + p * h) + g)) →
      EuclideanSpace ℝ (Fin (H * N + M * H)) := fun y => pc (Φ (cc.symm y)) with hψ
  have hpcU : ∀ x ∈ U, pc.symm x ∈ O := by
    rintro _ ⟨w, hw, rfl⟩
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  have hccV : ∀ y ∈ V, cc.symm y ∈ O' := by
    rintro _ ⟨z, hz, rfl⟩
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  have hmaps : Set.MapsTo φ U V := fun x hx => ⟨Ψ (pc.symm x), hbij.mapsTo (hpcU x hx), rfl⟩
  have hΦmaps : Set.MapsTo Φ O' O := hinvOn.1.mapsTo hbij.surjOn
  have hmapsψ : Set.MapsTo ψ V U := fun y hy => ⟨Φ (cc.symm y), hΦmaps (hccV y hy), rfl⟩
  have hinv : Set.InvOn ψ φ U V := by
    constructor
    · intro x hx
      show pc (Φ (cc.symm (cc (Ψ (pc.symm x))))) = x
      rw [ContinuousLinearEquiv.symm_apply_apply, hinvOn.1 (hpcU x hx),
        ContinuousLinearEquiv.apply_symm_apply]
    · intro y hy
      show cc (Ψ (pc.symm (pc (Φ (cc.symm y))))) = y
      rw [ContinuousLinearEquiv.symm_apply_apply, hinvOn.2 (hccV y hy),
        ContinuousLinearEquiv.apply_symm_apply]
  have hφan : AnalyticOnNhd ℝ φ U :=
    AnalyticOnNhd.comp' (analyticOnNhd_continuousLinearEquiv cc _)
      (AnalyticOnNhd.comp hΨ
        (analyticOnNhd_continuousLinearEquiv (pc.symm) U) hpcU)
  have hψan : AnalyticOnNhd ℝ ψ V :=
    AnalyticOnNhd.comp' (analyticOnNhd_continuousLinearEquiv pc _)
      (AnalyticOnNhd.comp hΦ
        (analyticOnNhd_continuousLinearEquiv (cc.symm) V) hccV)
  -- the pair of the transported germ
  have hφw₀ : φ w₀ = 0 := by
    show cc (Ψ (pc.symm (matrixPairEquiv M N H (Astar, Bstar)))) = 0
    rw [show pc.symm (matrixPairEquiv M N H (Astar, Bstar)) = (Astar, Bstar) from
      pc.symm_apply_apply (Astar, Bstar), hΨ0, map_zero]
  have htrans : HasLocalVolumeOrder (chartGerm q p h n g ∘ φ) w₀ lam m :=
    hasLocalVolumeOrder_comp_of_analytic' hdim hUopen hVopen hw₀U hmaps hinv hφan hψan
      (by rw [hφw₀]; exact hpair)
  -- Lemma 6.2 against print's constants, halved because the chart bounds `2K`
  refine hasLocalVolumeOrder_of_comparable (c₁ := 1 / 24) (c₂ := 3) (by norm_num) (by norm_num)
    ?_ htrans
  filter_upwards [hUopen.mem_nhds hw₀U] with x hx
  have hxO : pc.symm x ∈ O := hpcU x hx
  have hg : (chartGerm q p h n g ∘ φ) x
      = comparisonGerm (Ψ (pc.symm x)).1 (Ψ (pc.symm x)).2.1 (Ψ (pc.symm x)).2.2.1 := by
    rw [Function.comp_apply, hφ]
    exact chartGerm_chartCoords q p h n g (Ψ (pc.symm x))
  have hb := hcomp (pc.symm x) hxO
  have hsymm : ((matrixPairEquiv M N H).symm x) = pc.symm x := rfl
  rw [hg, hsymm]
  constructor
  · linarith [hb.1]
  · linarith [hb.2]

/-! ## At the canonical representative of a feasible stratum

`ChartAssembly.lean` proves Theorem 5.1 unconditionally at every feasible stratum. Feeding it to
the transport gives the pair of the loss at the canonical representative, with the chart germ's
pair as the only remaining input.
-/

/-- **Print's steps 2 to 6 at the canonical representative.** At a feasible stratum the chart
exists, so the pair of the comparison germ at the origin of the chart space is the pair of the
loss at `(A*, B*)`. -/
public theorem hasLocalVolumeOrder_rrrLoss_canonical
    {M N H r a b : ℕ} (hra : r ≤ a) (hrb : r ≤ b) (hab : a + b ≤ H + r)
    (haN : a ≤ N) (hbM : b ≤ M) {lam : ℝ} {m : ℕ}
    (hpair : HasLocalVolumeOrder
      (chartGerm (elimQ M N a b) (elimP M b) (elimH H r a b) (elimN N a)
        (elimGauge M N H r a b)) 0 lam m) :
    HasLocalVolumeOrder
      (fun x => rrrLoss (partialIdMatrix M N r) ((matrixPairEquiv M N H).symm x).1
        ((matrixPairEquiv M N H).symm x).2)
      (matrixPairCoords (canonicalA N H a b r) (canonicalB M H b r)) lam m := by
  have hdim : H * N + M * H
      = elimQ M N a b + (elimH H r a b * elimN N a + elimP M b * elimH H r a b)
        + elimGauge M N H r a b := by
    rw [← elim_dimension_split hbM haN hra hrb hab]; ring
  exact hasLocalVolumeOrder_rrrLoss_coords hdim
    (isEliminationChart_of_feasible hra hrb hab haN hbM) hpair

end AISafetyAtlas.SingularLearning
