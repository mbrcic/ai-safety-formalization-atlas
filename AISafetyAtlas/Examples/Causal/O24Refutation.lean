module

public import AISafetyAtlas.Analysis.PolynomialGenericity
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Topology.Algebra.MvPolynomial
public import AISafetyAtlas.Causal.EffectiveGenericity
public import AISafetyAtlas.Examples.Causal.BehavioralCollision

/-!
# MAIS-O24's conclusions (a) and (c) are incompatible

The candidate negative resolution submitted as `lionellevine/MAIS`
[issue #7](https://github.com/lionellevine/MAIS/issues/7) (2026-08-04), checked
here: **no polynomial list can satisfy `prob:effective`'s conclusions (a) and
(c) at once**, whatever the requested size and time bounds say.

## The argument

MAIS-O23's collision, already in this tree, is a *point*. Conclusion (a) is
violated by a whole **open box** of them, and that is what the argument needs:
the utility gap `g = ½ - 1_{(1,1)}` reads the `(1,1)` cell and nothing else, and
at that cell an `X → Y` model and the edgeless model carrying its `X = 1` row
agree by construction — the source row `q₀` is behaviourally invisible. Vary all
three table entries in a box and the collision persists.

So at every point of the box, one of the two graphs' polynomials must vanish, or
(a) would identify two models with different graphs. A finite union of zero sets
of *nonzero* polynomials is null, and the box is not; hence one polynomial is
identically zero along the box at that utility.

Conclusion (c) is then contradicted, but not at that utility — (c) is asserted
only almost everywhere, and nothing says the collision utility is not in the null
set it may discard. The vanishing is instead pushed to *nearby* utilities: the
evaluation map is continuous and the table box is compact, so at utilities close
enough to the collision the same polynomial is uniformly smaller than any given
`μ`, and the whole box lands in (c)'s excluded set while (c)'s own bound
`S^a μ^b` tends to zero.

## One quantifier that has to be handled with care

`prob:effective` puts `∀ μ` **outside** the three conclusions, so (c)'s
almost-every quantifier sits inside it and the null set (c) discards may depend
on `μ`. `O24ExcludedSetSmall` keeps that order, which makes the point visible:
the submitted note picks the utilities first, sets `s_n` to the polynomial's
supremum at each, and only then builds `μ_n` from `s_n` — so the null set it
must avoid is still free to depend on the `μ` its own choice produced. The
argument is circular as written.

The repair is to **reverse the order**, not to strengthen anything. `μ` here is
fixed from `S`, `a`, `b` and the volume of the compact table box alone, none of
which mention a utility; the utility is chosen afterwards, from the
positive-measure set on which (c) is asserted at that one `μ`. No countable
union, and no reading of (c) beyond print's.

## What this costs the rest of the agenda

`AISafetyAtlas.Examples.Causal.EffectiveGenericity` records that `O24Solution`
having no inhabitant is expected — `prob:effective` is open — but that the
*fields being jointly contradictory* is a different and unwelcome reason, since
it makes every downstream *"for every solution to MAIS-O24, …"* vacuously true.
`isEmpty_o24Solution` shows the fields **are** jointly contradictory. MAIS-O26
(`CONJ-003`) is stated over exactly that quantifier and is therefore vacuous as
printed; that is a fact about `conj:exact`, not a defect introduced here.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Causal.O24Refutation

open AISafetyAtlas.Causal
open AISafetyAtlas.Examples.Causal
open MvPolynomial MeasureTheory

/-! ## The two graphs

`prob:effective` supplies one list per compatible graph, and the collision pairs
a one-edge graph with the edgeless one. Both are read off the models MAIS-O23's
collision already carries, so acyclicity comes with them. -/

/-- The `X → Y` graph. -/
@[expose] public def arrowG : Fin 2 → Finset (Fin 2) := arrowXY.parents

/-- The edgeless graph. -/
@[expose] public def edgeG : Fin 2 → Finset (Fin 2) := edgeless.parents

public theorem arrowG_apply (c : Fin 2) : arrowG c = if c = Y then {X} else ∅ := rfl

public theorem edgeG_apply (c : Fin 2) : edgeG c = ∅ := rfl

public theorem arrowG_acyclic : ∃ rank : Fin 2 → ℕ, ∀ c, ∀ p ∈ arrowG c, rank p < rank c :=
  arrowXY.acyclic

public theorem edgeG_acyclic : ∃ rank : Fin 2 → ℕ, ∀ c, ∀ p ∈ edgeG c, rank p < rank c :=
  edgeless.acyclic

public theorem arrowG_compatible : IsCompatibleGraph arrowG := arrowG_acyclic

public theorem edgeG_compatible : IsCompatibleGraph edgeG := edgeG_acyclic

/-- The two graphs are different, which is what makes the collision a failure of
conclusion (a) rather than a repetition. -/
public theorem arrowG_ne_edgeG : arrowG ≠ edgeG := by
  intro h
  have := congrFun h Y
  simp [arrowG_apply, edgeG_apply] at this

/-! ## The chart box the collision lives on

Conclusion (a) is stated over models and (c) over chart points, so the family is
carried as chart points and turned into models by `Model.ofChart`. -/

/-- The parent bit an `X → Y` chart index carries: the value of `X` in `Y`'s
row, and `0` in `X`'s own row, which has no parents. -/
@[expose] public def arrowBit (i : ChartIndex arrowG) : Fin 2 :=
  if h : X ∈ arrowG i.1 then i.2 ⟨X, h⟩ else 0

/-- The box's lower corner: MAIS issue #7's own box, `p ∈ (0.45, 0.55)`,
`q₀ ∈ (0.15, 0.25)`, `q₁ ∈ (0.75, 0.85)`. -/
@[expose] public noncomputable def o24Lo (i : ChartIndex arrowG) : ℝ :=
  if i.1 = Y then (if arrowBit i = 1 then 3 / 4 else 3 / 20) else 9 / 20

/-- The box's upper corner. -/
@[expose] public noncomputable def o24Hi (i : ChartIndex arrowG) : ℝ :=
  if i.1 = Y then (if arrowBit i = 1 then 17 / 20 else 1 / 4) else 11 / 20

public theorem o24Lo_lt_hi (i : ChartIndex arrowG) : o24Lo i < o24Hi i := by
  unfold o24Lo o24Hi
  split_ifs <;> norm_num

/-- Every point of the box is a table entry between `3/20` and `17/20`, which is
what (M1) at `λ = 1/10` needs with room to spare. -/
public theorem o24Lo_lower (i : ChartIndex arrowG) : (3 : ℝ) / 20 ≤ o24Lo i := by
  unfold o24Lo; split_ifs <;> norm_num

public theorem o24Hi_upper (i : ChartIndex arrowG) : o24Hi i ≤ (17 : ℝ) / 20 := by
  unfold o24Hi; split_ifs <;> norm_num

/-- **The open box of colliding parameters.** -/
@[expose] public noncomputable def o24Box : Set (ChartIndex arrowG → ℝ) :=
  Set.pi Set.univ fun i ↦ Set.Ioo (o24Lo i) (o24Hi i)

public theorem mem_o24Box_bounds {θ : ChartIndex arrowG → ℝ} (hθ : θ ∈ o24Box)
    (i : ChartIndex arrowG) : (3 : ℝ) / 20 < θ i ∧ θ i < 17 / 20 := by
  have h := hθ i (Set.mem_univ i)
  exact ⟨lt_of_le_of_lt (o24Lo_lower i) h.1, lt_of_lt_of_le h.2 (o24Hi_upper i)⟩

public theorem mem_o24Box_unitInterval {θ : ChartIndex arrowG → ℝ} (hθ : θ ∈ o24Box)
    (i : ChartIndex arrowG) : 0 ≤ θ i ∧ θ i ≤ 1 := by
  obtain ⟨h0, h1⟩ := mem_o24Box_bounds hθ i
  constructor <;> linarith

/-! ## The colliding pair at a chart point

Every point of the box carries two models: the `X → Y` model it *is*, and the
edgeless model reading each table at the parent configuration `X = 1`. The
source row `q₀` is discarded, and that is exactly what the transform cannot
see. -/

/-- The edgeless chart matched to an `X → Y` chart: every table read at the
parent configuration `X = 1`. -/
@[expose] public noncomputable def matchedEdgeChart (θ : ChartIndex arrowG → ℝ) :
    ChartIndex edgeG → ℝ :=
  fun i ↦ θ ⟨i.1, fun _ ↦ 1⟩

/-- The `X → Y` model at a chart point. -/
@[expose] public noncomputable def arrowModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) : Model (Fin 2) (binaryDim (Fin 2)) ℝ :=
  Model.ofChart arrowG arrowG_acyclic θ hθ

/-- The edgeless model carrying that point's `X = 1` row. -/
@[expose] public noncomputable def edgeModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) : Model (Fin 2) (binaryDim (Fin 2)) ℝ :=
  Model.ofChart edgeG edgeG_acyclic (matchedEdgeChart θ) fun i ↦ hθ ⟨i.1, fun _ ↦ 1⟩

@[simp] public theorem parents_arrowModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) : (arrowModel hθ).parents = arrowG :=
  Model.parents_ofChart _ _ _ _

@[simp] public theorem parents_edgeModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) : (edgeModel hθ).parents = edgeG :=
  Model.parents_ofChart _ _ _ _

@[simp] public theorem chartOn_arrowModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) : (arrowModel hθ).chartOn arrowG = θ :=
  Model.chartOn_ofChart _ _ _ _

@[simp] public theorem chartOn_edgeModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) :
    (edgeModel hθ).chartOn edgeG = matchedEdgeChart θ :=
  Model.chartOn_ofChart _ _ _ _

/-- The two models are distinct, because their graphs are. -/
public theorem arrowModel_ne_edgeModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) : arrowModel hθ ≠ edgeModel hθ := by
  refine Model.ne_of_parents_ne ?_
  rw [parents_arrowModel, parents_edgeModel]
  exact arrowG_ne_edgeG

/-- Every variable is set to `1` at the assignment the gap is supported on. -/
public theorem asg_true_true_apply (c : Fin 2) : asg true true c = 1 := by
  fin_cases c <;> rfl

/-- **The tables agree at `(1,1)`.** For the `X → Y` model the parent
configuration read there is `X = 1`, which is the row the edgeless model was
given; for the edgeless model there is no configuration to read. -/
public theorem cpt_eq_at_true {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) (c : Fin 2) (a : Fin (binaryDim (Fin 2) c)) :
    (arrowModel hθ).cpt c a (asg true true) = (edgeModel hθ).cpt c a (asg true true) := by
  have hcfg : (fun p : arrowG c ↦ (asg true true) p.1) = fun _ ↦ (1 : Fin 2) :=
    funext fun p ↦ asg_true_true_apply p.1
  simp only [arrowModel, edgeModel, Model.ofChart, matchedEdgeChart, hcfg]

/-- **The collision, at the level of the one cell the gap weights.** -/
public theorem jointProb_eq_at_true {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1)
    (σ : InterventionProfile (Fin 2) (binaryDim (Fin 2))) :
    (arrowModel hθ).jointProb σ (asg true true) =
      (edgeModel hθ).jointProb σ (asg true true) :=
  Model.jointProb_congr_at _ _ σ _ (cpt_eq_at_true hθ)

/-- `g = ½ - 1_{(1,1)}` over `ℝ`, so the transform reads the `(1,1)` cell only.
The rational form is `Examples.Causal.Δ_eq_half_sub_joint`; the box is a real
family and is not the image of a rational one. -/
public theorem Δ_eq_half_sub_joint_real (M : Model (Fin 2) (binaryDim (Fin 2)) ℝ)
    (σ : InterventionProfile (Fin 2) (binaryDim (Fin 2))) :
    M.Δ (skel.mapRat ℝ).gap σ = 1 / 2 - M.jointProb σ (asg true true) := by
  have hg : ∀ v, (skel.mapRat ℝ).gap v = ((g v : ℚ) : ℝ) := fun v ↦ by
    rw [Skeleton.gap_mapRat, skel_gap]
  unfold Model.Δ
  have hsum := jointProb_sum_two M σ
  rw [sum_assignment_two] at hsum ⊢
  simp only [hg]
  norm_num [g, asg, binaryState] at hsum ⊢
  linarith

/-- **The collision on the whole box**, at every deterministic profile. -/
public theorem collision_box {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1)
    (σ : InterventionProfile (Fin 2) (binaryDim (Fin 2))) :
    (arrowModel hθ).Δ (skel.mapRat ℝ).gap σ = (edgeModel hθ).Δ (skel.mapRat ℝ).gap σ := by
  rw [Δ_eq_half_sub_joint_real, Δ_eq_half_sub_joint_real, jointProb_eq_at_true]

/-- **The behavioural family collides.** `𝐎 = ∅`, so the family has the single
component `Δ^∅` and profile-wise agreement is the whole of it. -/
public theorem behaviorEq_box {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) :
    (skel.mapRat ℝ).BehaviorEq (arrowModel hθ) (edgeModel hθ) :=
  Skeleton.behaviorEq_of_observed_eq_empty rfl fun _ ↦
    Model.Δmix_congr _ _ _ _ (collision_box hθ)

/-! ## Freezing the utility

Conclusion (a) reads a certificate at a model, which carries both `θ` and `u`;
conclusion (c) reads it at a `θ` with `u` fixed. `spec` is the bridge: the
certificate with the utility substituted, a polynomial in the table coordinates
alone. -/

/-- The collision skeleton's utility, in conclusion (c)'s coordinates. -/
@[expose] public noncomputable def u₀ :
    Bool × UtilityConfig (skel.mapRat ℝ).utilityParents → ℝ :=
  fun dz ↦ (skel.mapRat ℝ).utility dz.1 dz.2.extend

/-- A certificate polynomial with the utility frozen at `u`. -/
@[expose] public noncomputable def spec {G : Fin 2 → Finset (Fin 2)}
    (u : Bool × UtilityConfig (skel.mapRat ℝ).utilityParents → ℝ)
    (q : MvPolynomial (O24Var (skel.mapRat ℝ).utilityParents G) ℚ) :
    MvPolynomial (ChartIndex G) ℝ :=
  MvPolynomial.bind₁ (Sum.elim MvPolynomial.X fun y ↦ MvPolynomial.C (u y))
    (MvPolynomial.map (algebraMap ℚ ℝ) q)

public theorem eval_spec {G : Fin 2 → Finset (Fin 2)}
    (u : Bool × UtilityConfig (skel.mapRat ℝ).utilityParents → ℝ)
    (q : MvPolynomial (O24Var (skel.mapRat ℝ).utilityParents G) ℚ)
    (θ : ChartIndex G → ℝ) :
    eval θ (spec u q) = aeval (Sum.elim θ u) q := by
  have hpt : (fun i ↦ aeval θ ((Sum.elim MvPolynomial.X fun y ↦ MvPolynomial.C (u y)) i))
      = Sum.elim θ u := by
    funext i
    -- `simp` no longer reduces `Sum.elim f g (Sum.inl a)` on its own, and the
    -- `aeval`/`algebraMap` step needs naming too.
    cases i <;>
      simp only [Sum.elim_inl, Sum.elim_inr, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  calc eval θ (spec u q)
      = aeval θ (MvPolynomial.bind₁ (Sum.elim MvPolynomial.X fun y ↦ MvPolynomial.C (u y))
          (MvPolynomial.map (algebraMap ℚ ℝ) q)) := rfl
    _ = aeval (Sum.elim θ u) (MvPolynomial.map (algebraMap ℚ ℝ) q) := by
          rw [MvPolynomial.aeval_bind₁, hpt]
    _ = eval (Sum.elim θ u) (MvPolynomial.map (algebraMap ℚ ℝ) q) := rfl
    _ = aeval (Sum.elim θ u) q := by
          rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

/-- The `θ`-point conclusion (a) reads at the `X → Y` model of a box point. -/
public theorem o24Point_arrowModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) :
    o24Point (skel.mapRat ℝ) (arrowModel hθ) arrowG = Sum.elim θ u₀ := by
  rw [o24Point, chartOn_arrowModel]
  rfl

/-- The same at the matched edgeless model. -/
public theorem o24Point_edgeModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) :
    o24Point (skel.mapRat ℝ) (edgeModel hθ) edgeG = Sum.elim (matchedEdgeChart θ) u₀ := by
  rw [o24Point, chartOn_edgeModel]
  rfl

/-! ## One variable set for both graphs

The edgeless certificate is a polynomial in two coordinates and the `X → Y` one
in three. Renaming along the injection that sends each edgeless coordinate to
the `X = 1` row puts both in the same ring, which is what a single covering
argument on the box needs. -/

/-- The coordinate injection: an edgeless index goes to the `X = 1` row. -/
@[expose] public def edgeIndex (i : ChartIndex edgeG) : ChartIndex arrowG :=
  ⟨i.1, fun _ ↦ 1⟩

public theorem matchedEdgeChart_eq (θ : ChartIndex arrowG → ℝ) :
    matchedEdgeChart θ = θ ∘ edgeIndex := rfl

public theorem edgeIndex_injective : Function.Injective edgeIndex := by
  rintro ⟨c, f⟩ ⟨d, h⟩ hcd
  have hc : c = d := congrArg Sigma.fst hcd
  subst hc
  have hfh : f = h := by
    funext q
    obtain ⟨x, hx⟩ := q
    rw [edgeG_apply] at hx
    exact absurd hx (Finset.notMem_empty x)
  rw [hfh]

public theorem eval_rename_edgeIndex (p : MvPolynomial (ChartIndex edgeG) ℝ)
    (θ : ChartIndex arrowG → ℝ) :
    eval θ (rename edgeIndex p) = eval (matchedEdgeChart θ) p := by
  rw [eval_rename, matchedEdgeChart_eq]

/-! ## A positive margin below a finite list of positive values -/

/-- A finite list of positive values has a positive lower bound. This is what
supplies the `μ` at which both colliding models sit inside `𝕄(sk, λ, μ)`. -/
public theorem exists_pos_le_of_forall_pos {α : Type*} (l : List α) (f : α → ℝ)
    (h : ∀ a ∈ l, 0 < f a) : ∃ ε > 0, ∀ a ∈ l, ε ≤ f a := by
  induction l with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons a t ih =>
    obtain ⟨ε, hε, hle⟩ := ih fun b hb ↦ h b (List.mem_cons_of_mem a hb)
    refine ⟨min (f a) ε, lt_min (h a (List.mem_cons_self ..)) hε, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (hle b hb)

/-! ## The box has positive volume -/

public theorem volume_o24Box_ne_zero : volume o24Box ≠ 0 := by
  rw [o24Box, MeasureTheory.volume_pi_pi]
  refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
  rw [Real.volume_Ioo, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  linarith [o24Lo_lt_hi i]

/-! ## The whole box lies in the margin class

Conclusion (a) is a statement about `𝕄(sk, λ, μ) ⊆ 𝕄(sk, λ)`, so the collision
only bites once both models are in the printed class at `λ = 1/10`. (M2), (M3)
and (M6) read the gap alone and are inherited from MAIS-O23's witness; (M5)
holds of every model on this skeleton because `𝐙 = 𝐂`; (M1) and (M4) are what
the box was chosen to give. -/

/-- The margin, over `ℝ`. -/
@[expose] public noncomputable def lamR : ℝ := 1 / 10

public theorem lam_cast : ((lam : ℚ) : ℝ) = lamR := by norm_num [lam, lamR]

public theorem validMargin_lamR : Skeleton.ValidMargin lamR := by
  constructor <;> norm_num [lamR]

/-- MAIS-O23's witness, cast, used only for the three gap-only conditions. -/
public theorem skel_real_base : (skel.mapRat ℝ).MarginClass (edgeless.mapRat ℝ) lamR :=
  lam_cast ▸ Skeleton.marginClass_mapRat (𝕝 := ℝ) edgeless_mem

public theorem skel_real_M2 : (skel.mapRat ℝ).M2 lamR := skel_real_base.2.2.1

public theorem skel_real_M3 : (skel.mapRat ℝ).M3 := skel_real_base.2.2.2.1

public theorem skel_real_M6 : (skel.mapRat ℝ).M6 lamR := skel_real_base.2.2.2.2.2.2

/-- (M5) holds of **every** model on this skeleton: `𝐙 = 𝐂` makes the closure
clause trivial and `𝐎 = ∅` is a proper subset. -/
public theorem skel_real_M5 (M : Model (Fin 2) (binaryDim (Fin 2)) ℝ) :
    (skel.mapRat ℝ).M5 M := by
  refine ⟨fun t ht _ ↦ Finset.univ_subset_iff.mp ?_, by decide⟩
  simpa [skel] using ht

public theorem M1_arrowModel {θ : ChartIndex arrowG → ℝ} (hbox : θ ∈ o24Box) :
    Skeleton.M1 (arrowModel (mem_o24Box_unitInterval hbox)) lamR := by
  intro c a v
  obtain ⟨h0, h1⟩ := mem_o24Box_bounds hbox ⟨c, fun p ↦ v p.1⟩
  simp only [arrowModel, Model.ofChart, lamR]
  split_ifs <;> constructor <;> linarith

public theorem M1_edgeModel {θ : ChartIndex arrowG → ℝ} (hbox : θ ∈ o24Box) :
    Skeleton.M1 (edgeModel (mem_o24Box_unitInterval hbox)) lamR := by
  intro c a v
  obtain ⟨h0, h1⟩ := mem_o24Box_bounds hbox ⟨c, fun _ ↦ 1⟩
  simp only [edgeModel, Model.ofChart, matchedEdgeChart, lamR]
  split_ifs <;> constructor <;> linarith

/-- The `X → Y` chart index at `Y`'s row reads its parent bit back. -/
public theorem arrowBit_Y (b : Fin 2) : arrowBit ⟨Y, fun _ ↦ b⟩ = b := by
  have hmem : X ∈ arrowG Y := by simp [arrowG_apply]
  simp [arrowBit, hmem]

/-- Every parent of `Y` in the `X → Y` graph is `X`. -/
public theorem arrowG_Y_parent (q : arrowG Y) : q.1 = X := by
  obtain ⟨x, hx⟩ := q
  simp only [arrowG_apply, if_pos, Finset.mem_singleton] at hx
  exact hx

/-- **(M4) on the box.** The edge `X → Y` is strong: the two rows are separated
by more than `1/2`, because the box puts `q₁` above `3/4` and `q₀` below
`1/4`. -/
public theorem M4_arrowModel {θ : ChartIndex arrowG → ℝ} (hbox : θ ∈ o24Box) :
    Skeleton.M4 (arrowModel (mem_o24Box_unitInterval hbox)) lamR := by
  intro c p hp
  rw [parents_arrowModel] at hp
  have hc : c = Y := by
    by_contra hne
    simp [arrowG_apply, hne] at hp
  subst hc
  have hpX : p = X := by
    simp only [arrowG_apply, if_pos, Finset.mem_singleton] at hp
    exact hp
  subst hpX
  refine ⟨asg true true, 1, 0, 1, by decide, ?_⟩
  have hrow : ∀ b : Fin 2,
      (arrowModel (mem_o24Box_unitInterval hbox)).cpt Y 1
        (Function.update (asg true true) X b) = θ ⟨Y, fun _ ↦ b⟩ := by
    intro b
    have hcfg : (fun q : arrowG Y ↦ (Function.update (asg true true) X b) q.1)
        = fun _ ↦ b := by
      funext q
      rw [arrowG_Y_parent q]
      simp
    simp only [arrowModel, Model.ofChart, hcfg, if_true]
  rw [hrow, hrow]
  have h1 := hbox ⟨Y, fun _ ↦ (1 : Fin 2)⟩ (Set.mem_univ _)
  have h0 := hbox ⟨Y, fun _ ↦ (0 : Fin 2)⟩ (Set.mem_univ _)
  simp only [o24Lo, o24Hi, arrowBit_Y] at h1 h0
  norm_num at h1 h0
  rw [abs_of_pos (by linarith [h1.1, h0.2])]
  simp only [lamR]
  linarith [h1.1, h0.2]

/-- (M4) is vacuous on the edgeless graph. -/
public theorem M4_edgeModel {θ : ChartIndex arrowG → ℝ} (hbox : θ ∈ o24Box) :
    Skeleton.M4 (edgeModel (mem_o24Box_unitInterval hbox)) lamR := by
  intro c p hp
  rw [parents_edgeModel] at hp
  simp [edgeG_apply] at hp

/-- **Both models of every box point are in the printed margin class.** -/
public theorem marginClass_arrowModel {θ : ChartIndex arrowG → ℝ} (hbox : θ ∈ o24Box) :
    (skel.mapRat ℝ).MarginClass (arrowModel (mem_o24Box_unitInterval hbox)) lamR :=
  ⟨validMargin_lamR, M1_arrowModel hbox, skel_real_M2, skel_real_M3,
    M4_arrowModel hbox, skel_real_M5 _, skel_real_M6⟩

public theorem marginClass_edgeModel {θ : ChartIndex arrowG → ℝ} (hbox : θ ∈ o24Box) :
    (skel.mapRat ℝ).MarginClass (edgeModel (mem_o24Box_unitInterval hbox)) lamR :=
  ⟨validMargin_lamR, M1_edgeModel hbox, skel_real_M2, skel_real_M3,
    M4_edgeModel hbox, skel_real_M5 _, skel_real_M6⟩

/-! ## Conclusion (a) kills a certificate polynomial on the box

At a box point where no supplied polynomial vanishes — at either graph — a small
enough `μ` puts *both* colliding models inside `𝕄(sk, λ, μ)`, and (a) then
identifies two models carrying different graphs. So some polynomial vanishes at
every point of the box; a finite list of nonzero polynomials cannot do that,
because the box is not null. -/

/-- **Some supplied polynomial vanishes at every box point.** -/
public theorem exists_o24Value_eq_zero (Q : O24Assignment (Fin 2))
    (hid : O24Identifies (skel.mapRat ℝ) Q)
    {θ : ChartIndex arrowG → ℝ} (hbox : θ ∈ o24Box) :
    (∃ q ∈ Q.at (skel.mapRat ℝ) arrowG, eval θ (spec u₀ q) = 0) ∨
      ∃ q ∈ Q.at (skel.mapRat ℝ) edgeG, eval (matchedEdgeChart θ) (spec u₀ q) = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hE⟩ := hcon
  obtain ⟨εA, hεA, hleA⟩ := exists_pos_le_of_forall_pos (Q.at (skel.mapRat ℝ) arrowG)
    (fun q ↦ |eval θ (spec u₀ q)|) fun q hq ↦ abs_pos.mpr (hA q hq)
  obtain ⟨εE, hεE, hleE⟩ := exists_pos_le_of_forall_pos (Q.at (skel.mapRat ℝ) edgeG)
    (fun q ↦ |eval (matchedEdgeChart θ) (spec u₀ q)|) fun q hq ↦ abs_pos.mpr (hE q hq)
  set hu := mem_o24Box_unitInterval hbox with _hudef
  set mu := min (min εA εE) (1 / 4) with _hmudef
  have hmuA : mu ≤ εA := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmuE : mu ≤ εE := le_trans (min_le_left _ _) (min_le_right _ _)
  have hmu : Skeleton.ValidMargin mu :=
    ⟨lt_min (lt_min hεA hεE) (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  have hMA : arrowModel hu ∈ effectiveMarginClass (skel.mapRat ℝ) lamR mu Q := by
    refine ⟨marginClass_arrowModel hbox, ?_⟩
    show ∀ q ∈ Q.at (skel.mapRat ℝ) arrowG, mu ≤ |o24Value (skel.mapRat ℝ) (arrowModel hu) q|
    intro q hq
    have hval : |o24Value (skel.mapRat ℝ) (arrowModel hu) q| = |eval θ (spec u₀ q)| := by
      rw [eval_spec, o24Value, o24Point_arrowModel]
    rw [hval]
    exact le_trans hmuA (hleA q hq)
  have hME : edgeModel hu ∈ effectiveMarginClass (skel.mapRat ℝ) lamR mu Q := by
    refine ⟨marginClass_edgeModel hbox, ?_⟩
    show ∀ q ∈ Q.at (skel.mapRat ℝ) edgeG, mu ≤ |o24Value (skel.mapRat ℝ) (edgeModel hu) q|
    intro q hq
    have hval : |o24Value (skel.mapRat ℝ) (edgeModel hu) q|
        = |eval (matchedEdgeChart θ) (spec u₀ q)| := by
      rw [eval_spec, o24Value, o24Point_edgeModel]
    rw [hval]
    exact le_trans hmuE (hleE q hq)
  exact arrowModel_ne_edgeModel hu
    (hid lamR mu validMargin_lamR hmu _ hMA _ hME (behaviorEq_box hu))

/-- **Conclusion (a) forces a supplied polynomial to be identically zero once the
utility is frozen at the collision skeleton's.** -/
public theorem exists_spec_eq_zero (Q : O24Assignment (Fin 2))
    (hid : O24Identifies (skel.mapRat ℝ) Q) :
    (∃ q ∈ Q.at (skel.mapRat ℝ) arrowG, spec u₀ q = 0) ∨
      ∃ q ∈ Q.at (skel.mapRat ℝ) edgeG, spec u₀ q = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hE⟩ := hcon
  set l : List (MvPolynomial (ChartIndex arrowG) ℝ) :=
    (Q.at (skel.mapRat ℝ) arrowG).map (spec u₀) ++
      (Q.at (skel.mapRat ℝ) edgeG).map (fun q ↦ rename edgeIndex (spec u₀ q)) with hl
  have hlne : ∀ r ∈ l, r ≠ 0 := by
    intro r hr
    rw [hl, List.mem_append] at hr
    rcases hr with hr | hr
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact hA q hq
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      intro h0
      exact hE q hq (MvPolynomial.rename_injective edgeIndex edgeIndex_injective
        (by simpa using h0))
  have hsub : o24Box ⊆ {x : ChartIndex arrowG → ℝ | ∃ r ∈ l, eval x r = 0} := by
    intro θ hθ
    rcases exists_o24Value_eq_zero Q hid hθ with ⟨q, hq, hz⟩ | ⟨q, hq, hz⟩
    · exact ⟨spec u₀ q, by rw [hl]; exact List.mem_append_left _ (List.mem_map.mpr ⟨q, hq, rfl⟩),
        hz⟩
    · refine ⟨rename edgeIndex (spec u₀ q), ?_, ?_⟩
      · rw [hl]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
      · rw [eval_rename_edgeIndex]
        exact hz
  exact volume_o24Box_ne_zero
    (measure_mono_null hsub (AISafetyAtlas.Analysis.volume_setOf_exists_eval_eq_zero l hlne))

/-! ## Conclusion (c) fails at the utilities beside the collision

The vanishing established above is at `u₀`, and (c) is asserted only for almost
every utility, so nothing yet contradicts it — `u₀` may be one of the utilities
(c) discards. What does contradict it is that the vanishing is *stable*: fix a
compact table box `K` and a margin `μ` small enough that (c)'s own bound
`S^a μ^b` is below `Leb(K)`; then by continuity every utility close enough to
`u₀` makes the same polynomial smaller than `μ` on all of `K`, and (c) is
asserted at some such utility because they form a set of positive measure.

**The order of the choices is the whole point.** `μ` is fixed from `S`, `a`, `b`
and `Leb(K)` alone — none of which depend on the utility — and only then is the
utility chosen. Choosing the utility first and building `μ` from it, which is how
the submitted note runs this step, leaves (c)'s null set free to depend on the
`μ` that the utility produced. -/

public theorem eval_map_eq_aeval {σ : Type*} (q : MvPolynomial σ ℚ) (x : σ → ℝ) :
    eval x (MvPolynomial.map (algebraMap ℚ ℝ) q) = aeval x q := by
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

/-- The collision skeleton's utility takes only the values `1/4` and `3/4`. -/
public theorem u_pos_lt_one (d : Bool) (v : Assignment (Fin 2) (binaryDim (Fin 2))) :
    0 < AISafetyAtlas.Examples.Causal.u d v ∧ AISafetyAtlas.Examples.Causal.u d v < 1 := by
  have h : g v = 1 / 2 ∨ g v = -(1 / 2) := by
    by_cases hv : v X = 1 ∧ v Y = 1
    · right; simp [g, hv]
    · left; simp [g, hv]
  cases d <;> rcases h with h | h <;>
    constructor <;> simp [AISafetyAtlas.Examples.Causal.u, h] <;> norm_num

/-- So `u₀` is interior to (c)'s utility box, and every neighbourhood of it meets
that box in a set of positive measure. -/
public theorem u₀_mem_Ioo (dz : Bool × UtilityConfig (skel.mapRat ℝ).utilityParents) :
    u₀ dz ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := u_pos_lt_one dz.1 dz.2.extend
  constructor
  · show (0 : ℝ) < ((AISafetyAtlas.Examples.Causal.u dz.1 dz.2.extend : ℚ) : ℝ)
    exact_mod_cast h0
  · show ((AISafetyAtlas.Examples.Causal.u dz.1 dz.2.extend : ℚ) : ℝ) < 1
    exact_mod_cast h1

/-- `S = K(G) + 2^{|𝐙|}` is at least one, so `S^a` is positive. -/
public theorem one_le_o24Size (Z : Finset (Fin 2)) (G : Fin 2 → Finset (Fin 2)) :
    1 ≤ o24Size Z G := by
  have h2 : 1 ≤ 2 ^ Z.card := Nat.one_le_two_pow
  simp only [o24Size]
  omega

/-- **Conclusion (c) fails once a supplied polynomial dies at the collision
utility.** -/
public theorem not_o24ExcludedSetSmall_of_spec_eq_zero
    (Q : O24Assignment (Fin 2)) (const : O24Constants)
    {G : Fin 2 → Finset (Fin 2)} (hG : IsCompatibleGraph G)
    {q : MvPolynomial (O24Var (skel.mapRat ℝ).utilityParents G) ℚ}
    (hq : q ∈ Q.at (skel.mapRat ℝ) G) (hzero : spec u₀ q = 0) :
    ¬ O24ExcludedSetSmall Q const := by
  intro hex
  classical
  set S := o24Size (skel.mapRat ℝ).utilityParents G with _hS
  set a := const.a (Fintype.card (Fin 2)) S with _ha
  set b := const.b (Fintype.card (Fin 2)) S with _hb
  have hbpos : 0 < b := const.b_pos _ _
  have hSpos : (0 : ℝ) < (S : ℝ) ^ a :=
    Real.rpow_pos_of_pos (by exact_mod_cast one_le_o24Size _ G) a
  -- the compact table box, and its volume
  set K : Set (ChartIndex G → ℝ) := Set.pi Set.univ fun _ ↦ Set.Icc (1 / 4 : ℝ) (3 / 4) with hK
  have hKcompact : IsCompact K := isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hKsub : K ⊆ chartBox G := by
    intro x hx i
    obtain ⟨h0, h1⟩ := hx i (Set.mem_univ i)
    refine ⟨by linarith, ?_⟩
    have : (0 : ℝ) + 1 = 1 := by norm_num
    rw [this]
    linarith
  set vK : ℝ := (1 / 2 : ℝ) ^ Fintype.card (ChartIndex G) with _hvK
  have hvKpos : 0 < vK := by positivity
  have hvolK : volume K = ENNReal.ofReal vK := by
    rw [hK, MeasureTheory.volume_pi_pi]
    have hone : ∀ i : ChartIndex G,
        volume (Set.Icc (1 / 4 : ℝ) (3 / 4)) = ENNReal.ofReal (1 / 2) := by
      intro _
      rw [Real.volume_Icc]
      norm_num
    rw [Finset.prod_congr rfl fun i _ ↦ hone i, Finset.prod_const, Finset.card_univ,
      ← ENNReal.ofReal_pow (by norm_num)]
  -- a margin small enough that (c)'s own bound is below the box's volume
  set c : ℝ := vK / (2 * ((S : ℝ) ^ a)) with hc
  have hcpos : 0 < c := by positivity
  set mu : ℝ := min (1 / 4) (c ^ (1 / b)) with _hmu
  have hmupos : 0 < mu := lt_min (by norm_num) (Real.rpow_pos_of_pos hcpos _)
  have hmuvalid : Skeleton.ValidMargin mu :=
    ⟨hmupos, lt_of_le_of_lt (min_le_left _ _) (by norm_num)⟩
  have hmub : mu ^ b ≤ c := by
    calc mu ^ b ≤ (c ^ (1 / b)) ^ b :=
          Real.rpow_le_rpow hmupos.le (min_le_right _ _) hbpos.le
      _ = c := by
          rw [← Real.rpow_mul hcpos.le, one_div, inv_mul_cancel₀ hbpos.ne', Real.rpow_one]
  have hbound : (S : ℝ) ^ a * mu ^ b < vK := by
    have h1 : (S : ℝ) ^ a * mu ^ b ≤ (S : ℝ) ^ a * c :=
      mul_le_mul_of_nonneg_left hmub hSpos.le
    have h2 : (S : ℝ) ^ a * c = vK / 2 := by
      rw [hc]
      field_simp
    linarith
  -- the polynomial is uniformly small on `K` at every nearby utility
  have hcont : Continuous fun p : (ChartIndex G → ℝ) ×
      ((Bool × UtilityConfig (skel.mapRat ℝ).utilityParents) → ℝ) ↦
      eval (Sum.elim p.1 p.2) (MvPolynomial.map (algebraMap ℚ ℝ) q) := by
    have hpair : Continuous fun p : (ChartIndex G → ℝ) ×
        ((Bool × UtilityConfig (skel.mapRat ℝ).utilityParents) → ℝ) ↦ Sum.elim p.1 p.2 := by
      refine continuous_pi fun i ↦ ?_
      cases i with
      | inl x => exact (continuous_apply x).comp continuous_fst
      | inr y => exact (continuous_apply y).comp continuous_snd
    exact (MvPolynomial.continuous_eval _).comp hpair
  set U : Set ((ChartIndex G → ℝ) ×
      ((Bool × UtilityConfig (skel.mapRat ℝ).utilityParents) → ℝ)) :=
    {p | |eval (Sum.elim p.1 p.2) (MvPolynomial.map (algebraMap ℚ ℝ) q)| < mu} with hU
  have hUopen : IsOpen U := isOpen_lt hcont.abs continuous_const
  have hKU : K ×ˢ ({u₀} : Set ((Bool × UtilityConfig (skel.mapRat ℝ).utilityParents) → ℝ))
      ⊆ U := by
    rintro ⟨θ, w⟩ ⟨-, hw⟩
    have hw' : w = u₀ := hw
    subst hw'
    have hz : eval (Sum.elim θ u₀) (MvPolynomial.map (algebraMap ℚ ℝ) q) = 0 := by
      rw [eval_map_eq_aeval, ← eval_spec, hzero, map_zero]
    simp only [hU, Set.mem_ofPred_eq, hz, abs_zero]
    exact hmupos
  obtain ⟨V₁, V₂, -, hV₂open, hKV₁, hV₂mem, hVU⟩ :=
    generalized_tube_lemma hKcompact isCompact_singleton hUopen hKU
  -- those utilities form a set of positive measure, so (c) is asserted at one
  set W : Set ((Bool × UtilityConfig (skel.mapRat ℝ).utilityParents) → ℝ) :=
    V₂ ∩ Set.pi Set.univ fun _ ↦ Set.Ioo (0 : ℝ) 1 with _hW
  have hWopen : IsOpen W :=
    hV₂open.inter (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo)
  have hWmem : u₀ ∈ W := ⟨hV₂mem rfl, fun i _ ↦ u₀_mem_Ioo i⟩
  have hWpos : volume W ≠ 0 := (hWopen.measure_pos volume ⟨u₀, hWmem⟩).ne'
  have hae := hex (skel.mapRat ℝ).observed (skel.mapRat ℝ).utilityParents G hG mu hmuvalid
  have hexists : ∃ w ∈ W, w ∈ utilityBox (skel.mapRat ℝ).utilityParents →
      volume (o24ExcludedSlice Q (skel.mapRat ℝ).observed
        (skel.mapRat ℝ).utilityParents G w mu) ≤ ENNReal.ofReal ((S : ℝ) ^ a * mu ^ b) := by
    by_contra hno
    refine hWpos (measure_mono_null ?_ (MeasureTheory.ae_iff.mp hae))
    intro x hx
    simp only [Set.mem_ofPred_eq]
    intro hcontra
    exact hno ⟨x, hx, hcontra⟩
  obtain ⟨w, hWw, hbnd⟩ := hexists
  have hwBox : w ∈ utilityBox (skel.mapRat ℝ).utilityParents := by
    intro i
    obtain ⟨h0, h1⟩ := hWw.2 i (Set.mem_univ i)
    refine ⟨h0.le, ?_⟩
    have : (0 : ℝ) + 1 = 1 := by norm_num
    rw [this]
    linarith
  have hKexcl : K ⊆ o24ExcludedSlice Q (skel.mapRat ℝ).observed
      (skel.mapRat ℝ).utilityParents G w mu := by
    intro θ hθ
    refine ⟨hKsub hθ, q, hq, ?_⟩
    have hin := hVU (Set.mk_mem_prod (hKV₁ hθ) hWw.1)
    rw [hU, Set.mem_ofPred_eq, eval_map_eq_aeval] at hin
    exact hin
  have hfinal : ENNReal.ofReal vK ≤ ENNReal.ofReal ((S : ℝ) ^ a * mu ^ b) := by
    rw [← hvolK]
    exact le_trans (measure_mono hKexcl) (hbnd hwBox)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfinal
  linarith

/-! ## The bundle is uninhabited

`not_o24_identifies_and_excluded` is the sharp form: it takes conclusions (a)
and (c) and nothing else, so the obstruction survives dropping conclusion (b),
the polynomial size bounds, and the construction-time clause. `O24Solution`
carries all of them, so it is empty a fortiori. -/

/-- **MAIS-O24's conclusions (a) and (c) are incompatible**, at the two-variable
skeleton, and with no use of (b), the size bounds, or the construction time. -/
public theorem not_o24_identifies_and_excluded (Q : O24Assignment (Fin 2))
    (const : O24Constants) (hid : O24Identifies (skel.mapRat ℝ) Q)
    (hex : O24ExcludedSetSmall Q const) : False := by
  rcases exists_spec_eq_zero Q hid with ⟨q, hq, hz⟩ | ⟨q, hq, hz⟩
  · exact not_o24ExcludedSetSmall_of_spec_eq_zero Q const arrowG_compatible hq hz hex
  · exact not_o24ExcludedSetSmall_of_spec_eq_zero Q const edgeG_compatible hq hz hex

/-- **`prob:effective` has no solution.** The bundle's fields are jointly
contradictory, so every downstream *"for every solution to MAIS-O24, …"* is
vacuously true — which is what `Examples.Causal.EffectiveGenericity` flagged as
the unwelcome reason `O24Solution` might be empty. -/
public theorem isEmpty_o24Solution : IsEmpty O24Solution :=
  ⟨fun sol ↦ not_o24_identifies_and_excluded (sol.lists 2) sol.constants
    (sol.identifies 2 (skel.mapRat ℝ)) (sol.excluded 2)⟩

end AISafetyAtlas.Examples.Causal.O24Refutation
