module

public import AISafetyAtlas.Causal.ParameterChart
public import AISafetyAtlas.Causal.Query

/-!
# A one-node margin class, and the identification it does support

MAIS-O25's eight-clause antecedent has no known inhabitant in the atlas so
far, so the conjecture could still be vacuously true once it is stated.

**This module builds the witness, one clause at a time.** One binary chance
variable, no observations, and a utility whose gap straddles zero. The margin
class there is exactly the interval `[λ, 1-λ]` of root probabilities, and all
eight clauses hold on it, with `K = 1`, `L = 10`, `ρ = 1 - 2λ` and `δmax = 1` —
each proved below. No declaration in the atlas assembles the eight into a
single antecedent at this commit; that assembly is conjecture-layer work,
downstream of this module.

The two substantive clauses are the sixth and the seventh.

**The sixth**, `behaviorEq_injective`: two models with equal behavioural families
are equal. MAIS-O23 is the statement that the unrestricted analogue is **false** —
margins alone do not identify in general — so it is worth naming what carries it
here rather than there. It is not the margin: the proof uses no margin hypothesis
at all. It is that a one-vertex graph is forced. `acyclic` forbids a self-parent,
`cpt_parents` then makes the table constant, and a model *is* its root
probability, which the observational transform reads off affinely.

**The seventh**, `modelError_le_ten_mul`: the linear recovery modulus, with the
constant `L = 10` exhibited rather than asserted. This is where the analyst's
freedom to *mix* interventions does the work. `AdmissibleFamily` quantifies over
the whole probability simplex on `InterventionProfile`, so for any two models
there is a mixture on which their advantages are equal in magnitude and opposite
in sign. One shared policy weight must then keep the regret under `δ` in both,
and because the two inequalities are on complementary weights they **add**, with
the weight cancelling. The zero-crossing on its own gives separation but no
modulus; the constant comes from centring.

**What this does not show.** It shows the antecedent is nonempty, which is the
vacuity question. It does not show the antecedent is *selective*: at one vertex
only the edgeless graph exists, so `K = 1`, the chart slice, and behavioural
injectivity all follow from the vertex set rather than from the class. `0 < rho`
inside `ContainsChartBox` is the one clause written to block a degenerate
witness, and `1 - 2λ = 4/5` meets it with room.
-/

namespace AISafetyAtlas.Examples.Causal.OneNodeClass

open AISafetyAtlas.Causal

/-! ## The skeleton -/

/-- The margin. -/
@[expose] public noncomputable def lam : ℝ := 1 / 10

/-- One binary chance variable, unobserved, read by the utility.

`observed = ∅` is what makes the policy a constant, and `M5` permits it: that
condition asks only for `observed ⊂ univ`. -/
@[expose] public noncomputable def sk : Skeleton (Fin 1) (binaryDim (Fin 1)) Bool ℝ where
  observed := ∅
  utilityParents := {0}
  utility := fun d v ↦
    if d then (if (v 0 : ℕ) = 1 then 9 / 10 else 1 / 10) else 1 / 2
  utility_parents := by
    intro d v w h
    have h0 : v 0 = w 0 := h 0 (by simp)
    simp [h0]
  utility_mem_unitInterval := by
    intro d v
    by_cases hd : d = true
    · subst hd
      by_cases h1 : (v 0 : ℕ) = 1 <;> simp [h1] <;> norm_num
    · have : d = false := by cases d <;> simp_all
      subst this
      norm_num

/-- The gap straddles zero: `+2/5` where the variable is `1`, `-2/5` where it is
`0`. Both have magnitude `2/5 ≥ λ`, and they differ by `4/5 ≥ λ`, which is what
`M2` and `M6` ask for. -/
public theorem sk_gap (v : Assignment (Fin 1) (binaryDim (Fin 1))) :
    sk.gap v = if (v 0 : ℕ) = 1 then 2 / 5 else -(2 / 5) := by
  simp only [Skeleton.gap, sk]
  by_cases h : (v 0 : ℕ) = 1 <;> simp [h] <;> norm_num

/-! ## The models

One free parameter: the root probability. `K(G) = 1` because the only graph on a
one-element vertex set is edgeless. -/

/-- The model with `P(C₁ = 1) = p`. -/
@[expose] public noncomputable def model (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    Model (Fin 1) (binaryDim (Fin 1)) ℝ where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun _ ↦ ∅
  acyclic := ⟨fun _ ↦ 0, by intro c q hq; simp at hq⟩
  cpt := fun _ a _ ↦ if (a : ℕ) = 1 then p else 1 - p
  cpt_parents := by intro c a v w _; rfl
  cpt_nonneg := by
    intro c a v
    by_cases h : (a : ℕ) = 1 <;> simp [h] <;> linarith
  cpt_sum := by
    intro c v
    simp [binaryDim, Fin.sum_univ_two]

public theorem model_parents (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (c : Fin 1) :
    (model p h0 h1).parents c = ∅ := rfl

/-- The root probability read back off the table. -/
public theorem model_cpt (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (a : Fin (binaryDim (Fin 1) 0)) (v : Assignment (Fin 1) (binaryDim (Fin 1))) :
    (model p h0 h1).cpt 0 a v = if (a : ℕ) = 1 then p else 1 - p := rfl

/-! ## One vertex forces the graph

Every fact in this module that looks like it is about the *class* is really
about the vertex set: `acyclic` cannot admit a self-parent at a single vertex,
so the parent set is empty, the table is constant, and `K(G) = 1` has no other
candidate. -/

/-- With one vertex no chance variable can have a parent: `acyclic` would have to
rank it strictly before itself. -/
public theorem parents_eq_empty (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ)
    (c : Fin 1) : M.parents c = ∅ := by
  obtain ⟨rank, hrank⟩ := M.acyclic
  refine Finset.eq_empty_of_forall_notMem fun q hq ↦ ?_
  have hlt := hrank c q hq
  rw [Subsingleton.elim q c] at hlt
  exact absurd hlt (lt_irrefl _)

/-- Tables over an empty parent set are constant in the assignment. -/
public theorem cpt_const (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ)
    (a : Fin 2) (v w : Assignment (Fin 1) (binaryDim (Fin 1))) :
    M.cpt 0 a v = M.cpt 0 a w :=
  M.cpt_parents 0 a v w (by rw [parents_eq_empty]; intro p hp; simp at hp)

/-- Both cells of the one table sum to one. -/
public theorem cpt_zero_eq (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ)
    (v : Assignment (Fin 1) (binaryDim (Fin 1))) :
    M.cpt 0 0 v = 1 - M.cpt 0 1 v := by
  have := M.cpt_sum 0 v
  rw [Fin.sum_univ_two] at this
  linarith

/-! ## The class is `𝕄(sk, λ)`, and it is what `prob:exact` asks for -/

public theorem lam_valid : Skeleton.ValidMargin lam := by
  constructor <;> norm_num [lam]

public theorem sk_M2 : sk.M2 lam := by
  intro v
  rw [sk_gap]
  by_cases h : (v 0 : ℕ) = 1 <;> simp [h, lam] <;> norm_num

public theorem sk_M3 : sk.M3 := by
  intro w
  refine ⟨fun _ ↦ 1, fun _ ↦ 0, ?_, ?_, ?_, ?_⟩
  · intro c hc; simp [sk] at hc
  · intro c hc; simp [sk] at hc
  · rw [sk_gap]; norm_num
  · rw [sk_gap]; norm_num

public theorem sk_M6 : sk.M6 lam := by
  intro j hj
  refine ⟨fun _ ↦ 0, 1, 0, ?_, ?_⟩
  · exact Fin.ne_of_val_ne (by norm_num)
  have hj0 : j = 0 := by simpa [sk] using hj
  subst hj0
  rw [sk_gap, sk_gap]
  norm_num [lam]

public theorem model_M1 {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (hlo : lam ≤ p) (hhi : p ≤ 1 - lam) : Skeleton.M1 (model p h0 h1) lam := by
  intro c a v
  rw [Subsingleton.elim c 0, model_cpt]
  by_cases h : (a : ℕ) = 1
  · simp [h]; exact ⟨hlo, hhi⟩
  · simp [h]
    constructor <;> linarith

public theorem model_M4 (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ) :
    Skeleton.M4 M lam := by
  intro c q hq
  rw [parents_eq_empty] at hq
  exact absurd hq (Finset.notMem_empty q)

public theorem sk_M5 (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ) : sk.M5 M := by
  constructor
  · intro t ht _
    refine Finset.eq_univ_of_forall fun c ↦ ?_
    have : (0 : Fin 1) ∈ t := ht (by simp [sk])
    simpa [Subsingleton.elim c 0] using this
  · refine Finset.ssubset_univ_iff.mpr ?_
    intro h
    have hmem : (0 : Fin 1) ∈ sk.observed := h ▸ Finset.mem_univ 0
    simp [sk] at hmem

/-- The six conditions reduce to `M1`: the other five are facts about the
skeleton and about the forced graph, not about the tables. -/
public theorem marginClass_of_M1 (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ)
    (h : Skeleton.M1 M lam) : sk.MarginClass M lam :=
  ⟨lam_valid, h, sk_M2, sk_M3, model_M4 M, sk_M5 M, sk_M6⟩

/-- **The one-node margin class.** Every root probability in `[λ, 1-λ]` gives a
member, and `def:margin`'s six conditions all hold. -/
public theorem model_marginClass {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (hlo : lam ≤ p) (hhi : p ≤ 1 - lam) :
    sk.MarginClass (model p h0 h1) lam :=
  marginClass_of_M1 _ (model_M1 h0 h1 hlo hhi)

/-- The class is **inhabited**, which is the first thing the eight-clause
antecedent needs and the thing an empty antecedent would fail. -/
public theorem marginClass_nonempty :
    ∃ M : Model (Fin 1) (binaryDim (Fin 1)) ℝ, sk.MarginClass M lam :=
  ⟨model (1 / 2) (by norm_num) (by norm_num),
    model_marginClass (by norm_num) (by norm_num) (by norm_num [lam])
      (by norm_num [lam])⟩

/-! ## Clause 6: behavioural identification on the class

The antecedent's sixth clause is `BehaviorEq M M' → M = M'`, and at
`observed = ∅` the behavioural family collapses onto `Δmix`, hence — by
`Δmix_eq_on_probMixture_iff` — onto the deterministic profiles. The
observational profile alone already separates: the transform reads the root
probability affinely with slope the gap difference, which `M2` keeps away from
zero.

MAIS-O23 says the unrestricted analogue is **false**; margins alone do not
identify in general. What makes one node different is that here the graph is
forced — with a single vertex `acyclic` forbids a self-parent, so `parents` is
empty and a model *is* its root probability. -/

/-- The two assignments on one binary variable. -/
private theorem sum_assignment (f : Assignment (Fin 1) (binaryDim (Fin 1)) → ℝ) :
    ∑ v, f v = f (fun _ ↦ 0) + f (fun _ ↦ 1) := by
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2))
    f (fun a ↦ f (fun _ ↦ a)) (fun v ↦ by congr 1; funext c; simp [Subsingleton.elim c 0])]
  simp [Fin.sum_univ_two]

/-- A one-vertex model is its root probability. -/
public theorem eq_of_cpt_one_eq {M M' : Model (Fin 1) (binaryDim (Fin 1)) ℝ}
    (h : M.cpt 0 1 (fun _ ↦ 0) = M'.cpt 0 1 (fun _ ↦ 0)) : M = M' := by
  refine Model.ext (funext fun c ↦ ?_) (funext fun c ↦ funext fun a ↦ funext fun v ↦ ?_)
  · rw [parents_eq_empty, parents_eq_empty]
  · obtain rfl : c = 0 := Subsingleton.elim c 0
    have hM : M.cpt 0 a v = M.cpt 0 a (fun _ ↦ 0) := cpt_const M a v _
    have hM' : M'.cpt 0 a v = M'.cpt 0 a (fun _ ↦ 0) := cpt_const M' a v _
    rw [hM, hM']
    by_cases ha : (a : ℕ) = 1
    · obtain rfl : a = 1 := Fin.ext (by simpa using ha)
      exact h
    · obtain rfl : a = 0 := Fin.ext (by
        have hlt := a.isLt
        simp only [binaryDim] at hlt
        simp only [Fin.val_zero]
        omega)
      rw [cpt_zero_eq, cpt_zero_eq, h]

/-- **The observational transform reads the root probability.** -/
public theorem delta_observational (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ) :
    M.Δ sk.gap (Model.observationalProfile (Fin 1) (binaryDim (Fin 1)))
      = (4 / 5) * M.cpt 0 1 (fun _ ↦ 0) - 2 / 5 := by
  rw [Model.Δ, sum_assignment]
  have hfac : ∀ v : Assignment (Fin 1) (binaryDim (Fin 1)),
      M.jointProb (Model.observationalProfile (Fin 1) (binaryDim (Fin 1))) v
        = M.cpt 0 (v 0) v := by
    intro v
    rw [Model.jointProb, Fin.prod_univ_one]
    simp only [Model.factor, Model.observationalProfile, identityIntervention, id_eq,
      Fin.isValue, Fin.sum_univ_two]
    by_cases h0 : (v 0 : ℕ) = 1
    · have hv : v 0 = 1 := Fin.ext (by simpa using h0)
      rw [hv]; norm_num
    · have hv : v 0 = 0 := Fin.ext (by
        have hlt := (v 0).isLt
        simp only [binaryDim] at hlt
        simp only [Fin.val_zero]
        omega)
      rw [hv]; norm_num
  rw [hfac, hfac, sk_gap, sk_gap]
  have h0 : M.cpt 0 0 (fun _ ↦ (0 : Fin 2)) = 1 - M.cpt 0 1 (fun _ ↦ (0 : Fin 2)) :=
    cpt_zero_eq M _
  have h1 : M.cpt 0 1 (fun _ ↦ (1 : Fin 2)) = M.cpt 0 1 (fun _ ↦ (0 : Fin 2)) :=
    cpt_const M 1 _ _
  norm_num [h0, h1]
  ring

/-- **Clause 6 of the eight-clause antecedent, on this class.** Two models whose
behavioural families agree are equal — no margin hypothesis is needed, because
the one-vertex graph is already forced. -/
public theorem behaviorEq_injective {M M' : Model (Fin 1) (binaryDim (Fin 1)) ℝ}
    (h : sk.BehaviorEq M M') : M = M' := by
  have hmix : ∀ w : ProbMixture (Fin 1) (binaryDim (Fin 1)) ℝ,
      M.Δmix sk.gap w.1 = M'.Δmix sk.gap w.1 := by
    intro w
    have := h ∅ (by simp) (fun _ ↦ 0) w
    rwa [Model.Δmask_empty, Model.Δmask_empty] at this
  have hprof := (Model.Δmix_eq_on_probMixture_iff M M' sk.gap).mp hmix
  have := hprof (Model.observationalProfile (Fin 1) (binaryDim (Fin 1)))
  rw [delta_observational, delta_observational] at this
  exact eq_of_cpt_one_eq (by linarith)

/-! ## Clause 7, step one: regret at a single visible fibre

`observed = ∅` forces `visible = ∅`, so a policy is one Bernoulli weight and the
regret is bounded below by the weight the policy puts on the *wrong* action times
the advantage. Both bounds hold with no case split on the advantage's sign, which
is what lets the two models' admissibility inequalities be added later. -/

/-- The single visible fibre. -/
@[expose] public def rep : Assignment (Fin 1) (binaryDim (Fin 1)) := fun _ ↦ 0

public theorem fibreRep_eq (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ)
    (v : Assignment (Fin 1) (binaryDim (Fin 1))) : fibreRep M ∅ v = rep := by
  funext c
  simp [fibreRep, rep]

public theorem image_fibreRep (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ) :
    Finset.univ.image (fibreRep M ∅) = {rep} := by
  rw [Finset.image_congr (g := fun _ ↦ rep) (fun v _ ↦ fibreRep_eq M v)]
  exact Finset.image_const Finset.univ_nonempty rep

/-- The advantage of the `true` decision is the behavioural transform. -/
public theorem fibreScore_sub (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ)
    (w : ProbMixture (Fin 1) (binaryDim (Fin 1)) ℝ) :
    M.fibreScore sk ∅ w rep true - M.fibreScore sk ∅ w rep false
      = M.Δmix sk.gap w.1 := by
  rw [M.fibreScore_true_sub_false sk ∅ w rep, Model.Δmask_empty]

/-- **Regret is at least the weight on the wrong action times the advantage**,
in both directions at once. -/
public theorem regret_ge (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ)
    (π : Policy (dim := binaryDim (Fin 1)) ∅ Bool ℝ)
    (w : ProbMixture (Fin 1) (binaryDim (Fin 1)) ℝ) :
    (1 - π.prob rep true) * M.Δmix sk.gap w.1 ≤ M.regret sk ∅ π w ∧
      -(π.prob rep true) * M.Δmix sk.gap w.1 ≤ M.regret sk ∅ π w := by
  have hA := fibreScore_sub M w
  have hsum := π.prob_sum rep
  rw [Fintype.sum_bool] at hsum
  have hvalue : M.value sk ∅ π w
      = M.fibreScore sk ∅ w rep false + π.prob rep true * M.Δmix sk.gap w.1 := by
    rw [Model.value, image_fibreRep, Finset.sum_singleton, Fintype.sum_bool]
    have hfalse : π.prob rep false = 1 - π.prob rep true := by linarith
    rw [hfalse, ← hA]
    ring
  have hopt : ∀ d : Bool, M.fibreScore sk ∅ w rep d ≤ M.optimalValue sk ∅ w := by
    intro d
    rw [Model.optimalValue, image_fibreRep, Finset.sum_singleton]
    exact M.fibreScore_le_best sk ∅ w rep d
  have h0 := hopt false
  have h1 := hopt true
  rw [Model.regret, hvalue]
  constructor <;> [linarith; linarith]

/-! ## Clause 7, step two: the two-point mixtures the analyst may ask for

`AdmissibleFamily` quantifies over the whole simplex on `InterventionProfile`, so
the analyst may pose `α · observe + (1-α) · do(b)`. The induced root probability
is `α·p` at `b = 0` and `1 - α(1-p)` at `b = 1`, which between them reach every
value in `[0, 1]` — and that is what identification at one node rests on. -/

/-- Observe. -/
@[expose] public def obsProf : InterventionProfile (Fin 1) (binaryDim (Fin 1)) :=
  Model.observationalProfile (Fin 1) (binaryDim (Fin 1))

/-- Force the single variable to `b`. -/
@[expose] public def doProf (b : Fin 2) : InterventionProfile (Fin 1) (binaryDim (Fin 1)) :=
  fixProfile (fun _ ↦ b)

public theorem obsProf_ne_doProf (b : Fin 2) : obsProf ≠ doProf b := by
  intro h
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 0) 1
  simp [obsProf, Model.observationalProfile, identityIntervention, doProf,
    fixProfile, fixIntervention] at h0 h1
  exact absurd (h0.trans h1.symm) (by decide)

/-- `α · observe + (1-α) · do(b)`. -/
@[expose] public noncomputable def mix (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (b : Fin 2) :
    ProbMixture (Fin 1) (binaryDim (Fin 1)) ℝ :=
  ⟨fun σ ↦ (if σ = obsProf then α else 0) + (if σ = doProf b then 1 - α else 0), by
    refine ⟨fun σ ↦ ?_, ?_⟩
    · have ha : (0 : ℝ) ≤ if σ = obsProf then α else 0 := by
        split_ifs
        · exact h0
        · exact le_rfl
      have hb : (0 : ℝ) ≤ if σ = doProf b then 1 - α else 0 := by
        split_ifs
        · linarith
        · exact le_rfl
      exact add_nonneg ha hb
    · rw [Finset.sum_add_distrib]
      simp⟩

/-- The transform of a two-point mixture. -/
public theorem Δmix_mix (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ)
    (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (b : Fin 2) :
    M.Δmix sk.gap (mix α h0 h1 b).1
      = α * M.Δ sk.gap obsProf + (1 - α) * M.Δ sk.gap (doProf b) := by
  rw [Model.Δmix_eq_sum]
  simp only [mix, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_congr rfl (g := fun σ ↦ if σ = obsProf then α * M.Δ sk.gap σ else 0)
      (fun σ _ ↦ by split_ifs <;> simp)]
    simp
  · rw [Finset.sum_congr rfl (g := fun σ ↦ if σ = doProf b then (1 - α) * M.Δ sk.gap σ else 0)
      (fun σ _ ↦ by split_ifs <;> simp)]
    simp

/-- Forcing the variable evaluates the gap there. -/
public theorem Δ_doProf (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ) (b : Fin 2) :
    M.Δ sk.gap (doProf b) = sk.gap (fun _ ↦ b) := by
  rw [Model.Δ]
  rw [Fintype.sum_eq_single (fun _ ↦ b)]
  · have : M.jointProb (doProf b) (fun _ ↦ b) = 1 := by
      rw [Model.jointProb, Fin.prod_univ_one, doProf, Model.factor_fixProfile]
      simp
    rw [this, one_mul]
  · intro v hv
    have hvb : v 0 ≠ b := by
      intro hcontra
      exact hv (funext fun c ↦ by rw [Subsingleton.elim c 0]; exact hcontra)
    have : M.jointProb (doProf b) v = 0 := by
      rw [Model.jointProb, Fin.prod_univ_one, doProf, Model.factor_fixProfile]
      simp [Ne.symm hvb]
    rw [this, zero_mul]

/-! ## Clause 7, step three: the centring mixture, and the constant

The advantage is affine in the induced root probability and crosses zero at
`1/2`. Choosing `α` so that the two models' induced probabilities sit
*symmetrically* about that crossing makes the two advantages equal in magnitude
and opposite in sign. One shared policy weight then has to pay for both, and
because the two admissibility inequalities are on complementary weights they
**add**, with the weight cancelling. That is where the constant comes from; the
zero-crossing on its own gives separation but no modulus. -/

/-- The transform of a two-point mixture, in the root probability. -/
public theorem Δmix_val (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ)
    (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (b : Fin 2) :
    M.Δmix sk.gap (mix α h0 h1 b).1
      = α * (4 / 5 * M.cpt 0 1 rep - 2 / 5)
        + (1 - α) * (if (b : ℕ) = 1 then 2 / 5 else -(2 / 5)) := by
  rw [Δmix_mix, obsProf, delta_observational, Δ_doProf, sk_gap]
  rfl

/-- Model error at one vertex is the distance between the root probabilities. -/
public theorem modelError_le (M M' : Model (Fin 1) (binaryDim (Fin 1)) ℝ) :
    modelError M M' ≤ |M.cpt 0 1 rep - M'.cpt 0 1 rep| := by
  have hpar : M.parents = M'.parents :=
    funext fun c ↦ by rw [parents_eq_empty, parents_eq_empty]
  rw [modelError, if_pos hpar]
  refine Finset.sup'_le _ _ fun c _ ↦ ?_
  obtain rfl : c = 0 := Subsingleton.elim c 0
  refine Finset.sup'_le _ _ fun av _ ↦ ?_
  have hM : M.cpt 0 av.1 av.2 = M.cpt 0 av.1 rep := cpt_const M av.1 av.2 rep
  have hM' : M'.cpt 0 av.1 av.2 = M'.cpt 0 av.1 rep := cpt_const M' av.1 av.2 rep
  rw [hM, hM']
  by_cases ha : (av.1 : ℕ) = 1
  · obtain h : av.1 = 1 := Fin.ext (by simpa using ha)
    rw [h]
  · obtain h : av.1 = 0 := Fin.ext (by
      have hlt := av.1.isLt
      simp only [binaryDim] at hlt
      simp only [Fin.val_zero]
      omega)
    rw [h, cpt_zero_eq, cpt_zero_eq]
    rw [show 1 - M.cpt 0 1 rep - (1 - M'.cpt 0 1 rep)
      = -(M.cpt 0 1 rep - M'.cpt 0 1 rep) by ring, abs_neg]

/-- **The two admissibility inequalities add.** A single shared policy weight
must keep the regret below `δ` in both models; on a mixture where the advantages
are `-m` and `+m` the weights are complementary, so `m ≤ 2δ` with the weight
cancelling. -/
public theorem magnitude_le_two_delta {M M' : Model (Fin 1) (binaryDim (Fin 1)) ℝ}
    {lam' δ m α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {b : Fin 2}
    (hid : InIdentifiedSet sk lam' δ M M')
    (hM : M.Δmix sk.gap (mix α h0 h1 b).1 = -m)
    (hM' : M'.Δmix sk.gap (mix α h0 h1 b).1 = m) : m ≤ 2 * δ := by
  obtain ⟨-, -, family, hadm, hadm'⟩ := hid
  set w := mix α h0 h1 b with hw
  set π := family ∅ (Finset.empty_subset sk.observed) w with hπ
  have hlow := (regret_ge M π w).2
  have hhigh := (regret_ge M' π w).1
  rw [hM] at hlow
  rw [hM'] at hhigh
  have hδM : M.regret sk ∅ π w ≤ δ := hadm ∅ (Finset.empty_subset sk.observed) w
  have hδM' : M'.regret sk ∅ π w ≤ δ := hadm' ∅ (Finset.empty_subset sk.observed) w
  have hcancel : -(π.prob rep true) * -m + (1 - π.prob rep true) * m = m := by ring
  linarith

/-- **One-sided recovery.** The centring `α` is `1/(p+p')` when the pair sits
above the crossing and `1/(2-(p+p'))` when it sits below; both land in `(0, 1]`
exactly on their own branch, and the branches overlap, so nothing falls through. -/
public theorem sub_le_ten_mul {M M' : Model (Fin 1) (binaryDim (Fin 1)) ℝ}
    {δ : ℝ} (hδ : 0 ≤ δ) (hid : InIdentifiedSet sk lam δ M M') :
    M'.cpt 0 1 rep - M.cpt 0 1 rep ≤ 10 * δ := by
  set p := M.cpt 0 1 rep with hp
  set p' := M'.cpt 0 1 rep with hp'
  have hpb := (hid.1.2.1) 0 1 rep
  have hp'b := (hid.2.1.2.1) 0 1 rep
  rw [← hp] at hpb
  rw [← hp'] at hp'b
  simp only [lam] at hpb hp'b
  by_cases hs : 1 ≤ p + p'
  · have hd : (0 : ℝ) < p + p' := by linarith
    have h0 : (0 : ℝ) ≤ 1 / (p + p') := by positivity
    have h1 : 1 / (p + p') ≤ 1 := by
      rw [div_le_one hd]; linarith
    have key := magnitude_le_two_delta (M := M) (M' := M') (b := 0)
      (m := 2 / 5 * (p' - p) / (p + p')) h0 h1 hid
      (by rw [Δmix_val]; norm_num; field_simp; ring)
      (by rw [Δmix_val]; norm_num; field_simp; ring)
    have hmul : 2 / 5 * (p' - p) / (p + p') * (p + p') = 2 / 5 * (p' - p) := by
      field_simp
    nlinarith [key, hd, hpb.2, hp'b.2]
  · have hs' : p + p' < 1 := lt_of_not_ge hs
    have hd : (0 : ℝ) < 2 - (p + p') := by linarith
    have h0 : (0 : ℝ) ≤ 1 / (2 - (p + p')) := by positivity
    have h1 : 1 / (2 - (p + p')) ≤ 1 := by
      rw [div_le_one hd]; linarith
    have key := magnitude_le_two_delta (M := M) (M' := M') (b := 1)
      (m := 2 / 5 * (p' - p) / (2 - (p + p'))) h0 h1 hid
      (by rw [Δmix_val]; norm_num; field_simp; ring)
      (by rw [Δmix_val]; norm_num; field_simp; ring)
    have hmul : 2 / 5 * (p' - p) / (2 - (p + p')) * (2 - (p + p'))
        = 2 / 5 * (p' - p) := by field_simp
    nlinarith [key, hd, hpb.1, hp'b.1]

/-- The identified set is symmetric: the shared family does not know which model
it was handed first. -/
public theorem inIdentifiedSet_symm {M M' : Model (Fin 1) (binaryDim (Fin 1)) ℝ}
    {lam' δ : ℝ} (hid : InIdentifiedSet sk lam' δ M M') :
    InIdentifiedSet sk lam' δ M' M := by
  obtain ⟨hM, hM', family, hadm, hadm'⟩ := hid
  exact ⟨hM', hM, family, hadm', hadm⟩

/-- **The recovery inequality on this class, with `L = 10`.** Both directions,
which is what `modelError`'s absolute value asks for. -/
public theorem modelError_le_ten_mul {M M' : Model (Fin 1) (binaryDim (Fin 1)) ℝ}
    {δ : ℝ} (hδ : 0 ≤ δ) (hid : InIdentifiedSet sk lam δ M M') :
    modelError M M' ≤ 10 * δ := by
  refine (modelError_le M M').trans ?_
  have hfwd := sub_le_ten_mul hδ hid
  have hbwd := sub_le_ten_mul hδ (inIdentifiedSet_symm hid)
  rw [abs_le]
  constructor <;> linarith

/-! ## Clauses 3, 5 and 8: the geometry

The remaining three clauses are all about the class's *table-parameter
projection*, and at one vertex there are only two graphs to consider. The
edgeless one projects onto the closed interval `[λ, 1-λ]`, which is compact,
semialgebraic, and a full-dimensional box of side `1-2λ` in the one coordinate
`K(G) = 1` provides. The self-looping one carries no model at all, so its
projection is empty and both conditions hold for the reason that costs nothing.

`0 < rho` in `ContainsChartBox` is the clause written to rule out a degenerate
witness, and `1 - 2λ = 4/5` meets it with room. -/

/-- The only graph a one-vertex model can carry. -/
@[expose] public def edgeless : Fin 1 → Finset (Fin 1) := fun _ ↦ ∅

public theorem edgeless_acyclic :
    ∃ rank : Fin 1 → ℕ, ∀ c, ∀ p ∈ edgeless c, rank p < rank c :=
  ⟨fun _ ↦ 0, by intro c q hq; simp [edgeless] at hq⟩

public theorem parents_eq_edgeless (M : Model (Fin 1) (binaryDim (Fin 1)) ℝ) :
    M.parents = edgeless :=
  funext fun c ↦ by rw [parents_eq_empty]; rfl

/-- `K(G) = 1`: one variable, no parents, one free table entry. -/
public theorem chartDim_edgeless : chartDim edgeless = 1 := by
  simp [chartDim, edgeless]

/-- A chart point of the box is the chart of a class member. -/
public theorem mem_chartSlice_of_mem_box {θ : ChartIndex edgeless → ℝ}
    (hθ : θ ∈ ClosedBox (fun _ ↦ lam) (1 - 2 * lam)) :
    θ ∈ Model.chartSlice {M | sk.MarginClass M lam} edgeless := by
  have hunit : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1 := by
    intro i
    obtain ⟨hlo, hhi⟩ := hθ i
    simp only [lam] at hlo hhi
    constructor <;> linarith
  refine ⟨Model.ofChart edgeless edgeless_acyclic θ hunit, ?_, by simp, ?_⟩
  · refine marginClass_of_M1 _ fun c a v ↦ ?_
    obtain ⟨hlo, hhi⟩ := hθ ⟨c, fun p ↦ v p.1⟩
    simp only [Model.ofChart, lam] at hlo hhi ⊢
    by_cases ha : a = 1 <;> simp [ha] <;> constructor <;> linarith
  · exact Model.chartOn_ofChart edgeless edgeless_acyclic θ hunit

/-- **The projection is exactly the box.** -/
public theorem chartSlice_edgeless :
    Model.chartSlice {M | sk.MarginClass M lam} edgeless
      = ClosedBox (fun _ ↦ lam) (1 - 2 * lam) := by
  ext θ
  constructor
  · rintro ⟨M, hM, -, rfl⟩
    intro i
    obtain ⟨hlo, hhi⟩ := hM.2.1 i.1 1 i.extend
    exact ⟨hlo, by simpa [Model.chartOn] using (by linarith : M.cpt i.1 1 i.extend ≤ lam + (1 - 2 * lam))⟩
  · exact mem_chartSlice_of_mem_box

/-- A graph with a self-loop carries no model, so its projection is empty. -/
public theorem chartSlice_eq_empty {G : Fin 1 → Finset (Fin 1)} (hG : G ≠ edgeless) :
    Model.chartSlice {M | sk.MarginClass M lam} G = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun θ hθ ↦ ?_
  obtain ⟨M, -, hpar, -⟩ := hθ
  exact hG (hpar ▸ parents_eq_edgeless M)

/-- **Clause 5.** -/
public theorem isCompactSemialgebraicClass :
    IsCompactSemialgebraicClass {M | sk.MarginClass M lam} := by
  intro G
  by_cases hG : G = edgeless
  · subst hG
    rw [chartSlice_edgeless]
    exact ⟨isCompact_closedBox _ _, isSemialgebraic_closedBox _ _⟩
  · rw [chartSlice_eq_empty hG]
    exact ⟨isCompact_empty, isSemialgebraic_empty⟩

/-- **Clause 8.** The box is the whole projection, and its side `1 - 2λ = 4/5` is
positive, which is the clause that blocks a degenerate singleton witness. -/
public theorem containsChartBox :
    ContainsChartBox {M | sk.MarginClass M lam} (1 - 2 * lam) := by
  exact ⟨by norm_num [lam], edgeless, fun _ ↦ lam, by rw [chartSlice_edgeless]⟩

/-! ## The recovery inequality is not vacuous, and `L` is not slack

`modelError_le_ten_mul` bounds `modelError` above, so it would hold for free if
`modelError` collapsed to zero on this class, or if `m` came out with the wrong
sign — `magnitude_le_two_delta` accepts a negative `m` without complaint. Neither
happens, and the two lemmas below are what say so rather than leaving it to
inspection. -/

/-- Model error at one vertex **is** the distance between the root
probabilities — not merely bounded by it. -/
public theorem modelError_eq (M M' : Model (Fin 1) (binaryDim (Fin 1)) ℝ) :
    modelError M M' = |M.cpt 0 1 rep - M'.cpt 0 1 rep| := by
  refine le_antisymm (modelError_le M M') ?_
  have hpar : M.parents = M'.parents :=
    funext fun c ↦ by rw [parents_eq_empty, parents_eq_empty]
  rw [modelError, if_pos hpar]
  refine le_trans ?_ (Finset.le_sup' (cptError M M') (Finset.mem_univ 0))
  exact Finset.le_sup' (fun av : Fin (binaryDim (Fin 1) 0) ×
    Assignment (Fin 1) (binaryDim (Fin 1)) ↦ |M.cpt 0 av.1 av.2 - M'.cpt 0 av.1 av.2|)
    (Finset.mem_univ (1, rep))

/-- **`L = 10` is doing work.** The two extreme members of the class are `4/5`
apart, so no shared policy family can be admissible for both below `δ = 2/25`.
An `L` smaller than `10` would have to beat this floor. -/
public theorem two_over_25_le_of_inIdentifiedSet {δ : ℝ} (hδ : 0 ≤ δ)
    (hid : InIdentifiedSet sk lam δ
      (model (1 / 10) (by norm_num) (by norm_num))
      (model (9 / 10) (by norm_num) (by norm_num))) :
    2 / 25 ≤ δ := by
  have hbound := modelError_le_ten_mul hδ hid
  rw [modelError_eq] at hbound
  have : |(1 : ℝ) / 10 - 9 / 10| = 4 / 5 := by rw [abs_of_nonpos] <;> norm_num
  rw [show (model (1 / 10) (by norm_num : (0:ℝ) ≤ 1/10) (by norm_num)).cpt 0 1 rep
      = 1 / 10 from rfl,
    show (model (9 / 10) (by norm_num : (0:ℝ) ≤ 9/10) (by norm_num)).cpt 0 1 rep
      = 9 / 10 from rfl, this] at hbound
  linarith

end AISafetyAtlas.Examples.Causal.OneNodeClass
