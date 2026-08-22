module

public import AISafetyAtlas.Causal.MarginClass

/-!
# Three causal models with one behavior

The construction submitted to MAIS as a candidate negative resolution of
**MAIS-O23** (*Do margins imply behavioral identifiability of causal models?*),
checked here.

## The claim being checked

MAIS-O23 asks: fix a skeleton and `λ ∈ (0, ½)`; if two models of the margin
class `M(s, λ)` have equal behavioral transforms, must they be equal?

The submission (`lionellevine/MAIS` issue #6, filed 2026-08-04, open and
unreviewed at the time of writing) answers **no**, with three distinct models on
two binary variables — the edgeless graph, `X → Y`, and `Y → X` — whose
transforms agree on every one of the sixteen local-intervention profiles.

Skeleton: `C = {X, Y}`, `O = ∅`, `Z = {X, Y}`, `λ = 1/10`, utility gap

```
g(x, y) = 1/2 - 1_{(x,y) = (1,1)}
```

and the three models

| graph | parameters |
|---|---|
| edgeless | `P(X=1) = 1/2`, `P(Y=1) = 4/5` |
| `X → Y` | `P(X=1) = 1/2`, `P(Y=1 ∣ X=0) = 1/5`, `P(Y=1 ∣ X=1) = 4/5` |
| `Y → X` | `P(Y=1) = 4/5`, `P(X=1 ∣ Y=0) = 4/5`, `P(X=1 ∣ Y=1) = 1/2` |

## Why it works

`g` is `1/2` everywhere except at `(1,1)`, so

```
Δ_M(σ) = 1/2 - P_M(X=1, Y=1 ; σ)
```

and the transform reads **only the `(1,1)` cell**. The three models'
observational marginals genuinely differ — `P(Y=1)` is `1/2` under `X → Y` but
`4/5` under the edgeless model — and no behavior can see that, because the
utility gap does not.

**Nothing cancels, and the distinction matters.** The agenda speaks of a
*cancellation mechanism* that a counterexample would reveal, but here no terms
cancel: the three models simply **agree** on the table values at the one
assignment `g` weights. At `(1,1)` all three have `P(X=1 ∣ ·) = 1/2` and
`P(Y=1 ∣ ·) = 4/5`, so the per-variable factors are equal one by one at every
profile, and the hard profiles force exactly this — `do(X=1)` makes `Δ` read
`P(Y=1 ∣ X=1)` and nothing else. The excluded locus is therefore an
intersection of *coordinate* conditions, not the vanishing locus of a generic
polynomial.

**What that says about the margin class.** Conditions (M2), (M3) and (M6)
constrain the gap's magnitude, its sign, and its sensitivity to each utility
parent — and this `g`, constant off a single `z`, satisfies all three. They do
not force `g` to be *rich*. A seventh condition bounding the gap's spread across
`dom(Z)` is the natural repair, and that is the actionable output of this
example for MAIS-O24.

## What is checked

* The transforms of all three models agree at **every** deterministic
  intervention pattern (`collision_edgeless_arrowXY`, `collision_edgeless_arrowYX`,
  `collision_arrowXY_arrowYX`); hence, by `Model.Δmix_congr`, at every ambient
  rational weight function (`collision_mix_edgeless_arrowXY` and companions),
  and therefore at every rational probability mixture. RE24's real simplex is
  not cast here. Since `O = ∅`, the transform *family* `(Δ^{O'})_{O' ⊆ O}` has
  the single component `Δ^∅ = Δ`, so this is equality of the whole family.
* All three models lie in the margin class at `λ = 1/10`: `edgeless_mem`,
  `arrowXY_mem`, `arrowYX_mem`, each a conjunction of six named conditions.
  **Where the weight sits, for a reviewer deciding where to push:** (M1) and (M4)
  are the only conditions the models have to earn. (M2), (M3) and (M6) depend on
  the gap alone, so they are proved once for the skeleton and shared; and (M5)
  holds for *any* model on this skeleton (`skel_M5`), because `Z = C` makes the
  ancestor condition automatic and `O = ∅` makes the hiding condition automatic.
* The models are pairwise distinct as graphs, and the shared transform is not
  degenerate — `transform_identity_edgeless` pins one of its values at `1/10`.

Together: `margin_class_not_identifiable`, two models of `M(s, λ)` at a margin
`λ ∈ (0, ½)`, distinct as graphs, with equal behavioral transforms — the full
family `(Δ^{O'})_{O' ⊆ O}`, not one component of it. **MAIS-O23, as transcribed
in `AISafetyAtlas.Causal.MarginClass`, is answered in the negative.**

`u` and `u_gap` exhibit a utility with values in `[0,1]` realizing the gap, so
the skeleton is one of the source's and not merely one satisfying the conditions
that are phrased in terms of `g`. The utility is now carried by `Skeleton`; the
two theorems sit beside `skel` because they are the concrete witness used to
construct it. The decision layer consumes this same stored utility.

**The masking layer is defined but not exercised here.** `O = ∅`, so
`Skeleton.BehaviorEq` quantifies over the single visible subset `∅` and the
family `(Δ^{O'})` has one member. That is what a counterexample to a statement
quantified over skeletons needs, and `(M5)` permits it (`O ⊊ C`), but a reviewer
should not read the headline as evidence about masking: the agenda's Remark 2.6
failure mode — the unmasked component non-injective while the family is
injective — is exactly what an example with no masks cannot exhibit. The family
layer is here so the *statement* is the source's, not because this example
tests it.

## What is a review question and not a build question

Whether that transcription is faithful to MAIS-A2 Definition 3.1. Three readings
carry the result and a reviewer should check each:

1. **The skeleton fixes no graph**, so the edgeless model belongs to `M(s, λ)`
   whenever the six conditions hold, and (M4) is vacuous for it. The agenda's
   §5 class `MM₂(λ)` is *not* this class — it is defined as the models carrying
   `G→` or `G←`. The result does not need the edgeless model: `arrowXY` and
   `arrowYX` alone are distinct and collide (`collision_mix_arrowXY_arrowYX`,
   `margin_class_not_identifiable_two_graphs`), so it survives the narrower
   reading too.
2. **(M3)'s slice condition** collapses, at `O = ∅`, to *`g` takes both signs*.
3. **This collision uses the gap.** The collision calculations read `g` (the
   derived `Skeleton.gap`), while the decision layer can read the stored `u`.
   `u_mem_unitInterval` and `u_gap` discharge the one thing that could go wrong
   — a gap no admissible utility realizes — for this skeleton.

**Not claimed:** priority. Issue #6 credits the prior construction in issue #4
(MAIS-O34, filed by a different author), and states that its own contribution is
making the O23 consequence explicit and extending it to all three graphs on two
binary variables. The atlas contributes the machine check, not the construction.
-/

namespace AISafetyAtlas.Examples.Causal

open AISafetyAtlas.Causal

local notation:max "Assignment" C:arg =>
  AISafetyAtlas.Causal.Assignment C (binaryDim C)
local notation:max "Model" C:arg =>
  AISafetyAtlas.Causal.Model C (binaryDim C) ℚ
local notation:max "InterventionProfile" C:arg =>
  AISafetyAtlas.Causal.InterventionProfile C (binaryDim C)
local notation:max "Mixture" C:arg =>
  AISafetyAtlas.Causal.Mixture C (binaryDim C) ℚ
local notation:max "Skeleton" C:arg =>
  AISafetyAtlas.Causal.Skeleton C (binaryDim C) Bool ℚ

namespace LocalIntervention

@[expose] public def identity : Fin 2 → Fin 2 := identityIntervention

@[expose] public def fix (b : Bool) : Fin 2 → Fin 2 := fixIntervention (binaryState b)

end LocalIntervention

@[expose] public def bernoulli (q : ℚ) (a : Fin 2) : ℚ := if a = 1 then q else 1 - q

/-- `X` is variable `0`. -/
public abbrev X : Fin 2 := 0
/-- `Y` is variable `1`. -/
public abbrev Y : Fin 2 := 1

/-- The utility gap `g(x, y) = 1/2 - 1_{(x,y) = (1,1)}`, of constant magnitude
`1/2` and taking both signs. -/
@[expose] public def g : Assignment (Fin 2) → ℚ :=
  fun v => if v X = 1 ∧ v Y = 1 then -(1/2) else 1/2

/-- The edgeless model: `P(X=1) = 1/2`, `P(Y=1) = 4/5`, independent. -/
@[expose] public def edgeless : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun _ => ∅
  acyclic := ⟨fun _ => 0, by intro c p hp; simp at hp⟩
  cpt := fun c a _ => bernoulli (if c = X then 1/2 else 4/5) a
  cpt_parents := by intro c a v w _; rfl
  cpt_nonneg := by
    intro c a v
    fin_cases a <;> simp [bernoulli] <;> split_ifs <;> norm_num
  cpt_sum := by
    intro c v
    rw [Fin.sum_univ_two]
    simp [bernoulli]

/-- The `X → Y` model: `P(X=1) = 1/2`, `P(Y=1 ∣ X=0) = 1/5`, `P(Y=1 ∣ X=1) = 4/5`. -/
@[expose] public def arrowXY : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun c => if c = Y then {X} else ∅
  acyclic := ⟨fun c => if c = Y then 1 else 0, by decide⟩
  cpt := fun c a v => bernoulli
    (if c = X then 1/2 else if v X = 1 then 4/5 else 1/5) a
  cpt_parents := by
    intro c a v w h
    fin_cases c
    · simp
    · have hX : v X = w X := h X (by simp)
      simp [hX]
  cpt_nonneg := by
    intro c a v
    fin_cases a <;> simp [bernoulli] <;> split_ifs <;> norm_num
  cpt_sum := by
    intro c v
    rw [Fin.sum_univ_two]
    simp [bernoulli]

/-- The `Y → X` model: `P(Y=1) = 4/5`, `P(X=1 ∣ Y=0) = 4/5`, `P(X=1 ∣ Y=1) = 1/2`. -/
@[expose] public def arrowYX : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun c => if c = X then {Y} else ∅
  acyclic := ⟨fun c => if c = X then 1 else 0, by decide⟩
  cpt := fun c a v => bernoulli
    (if c = Y then 4/5 else if v Y = 1 then 1/2 else 4/5) a
  cpt_parents := by
    intro c a v w h
    fin_cases c
    · have hY : v Y = w Y := h Y (by simp)
      simp [hY]
    · simp
  cpt_nonneg := by
    intro c a v
    fin_cases a <;> simp [bernoulli] <;> split_ifs <;> norm_num
  cpt_sum := by
    intro c v
    rw [Fin.sum_univ_two]
    simp [bernoulli]

/-- There are sixteen local-intervention profiles on two variables: two
coordinates, each ranging over the four self-maps of `Fin 2`. RE24 Definition 2
states the profile space this counts; the number sixteen is not itself printed
anywhere in RE24. -/
public theorem card_profiles : Fintype.card (InterventionProfile (Fin 2)) = 16 := by
  change Fintype.card ((c : Fin 2) → Fin 2 → Fin 2) = 16
  decide

/-- The printed identity that explains the collision: this `g` is `1/2` off
`(1,1)` and `-1/2` there, so `Δ_M(σ) = 1/2 - P_M(1,1 ; σ)`. The `1/2` term
comes from `jointProb_sum`, the atlas's own normalization theorem for every
local-intervention profile — not from Pearl (1.37), which states the truncated
factorization for hard interventions only and does not cover the profiles this
theorem quantifies over. -/
public theorem Δ_eq_half_sub_joint (M : Model (Fin 2)) (σ : InterventionProfile (Fin 2)) :
    M.Δ g σ = 1/2 - M.jointProb σ (asg true true) := by
  unfold Model.Δ
  have hsum := jointProb_sum_two M σ
  rw [sum_assignment_two] at hsum ⊢
  norm_num [g, asg, binaryState] at hsum ⊢
  linarith

/-- **The collision, first pair.** The edgeless model and the `X → Y` model have
the same behavioral transform at every one of the sixteen profiles. -/
public theorem collision_edgeless_arrowXY (σ : InterventionProfile (Fin 2)) :
    edgeless.Δ g σ = arrowXY.Δ g σ := by
  rw [Δ_eq_half_sub_joint, Δ_eq_half_sub_joint]
  congr 1

/-- **The collision, second pair.** The edgeless model and the `Y → X` model
have the same behavioral transform at every one of the sixteen profiles. -/
public theorem collision_edgeless_arrowYX (σ : InterventionProfile (Fin 2)) :
    edgeless.Δ g σ = arrowYX.Δ g σ := by
  rw [Δ_eq_half_sub_joint, Δ_eq_half_sub_joint]
  congr 1

/-- All three transforms agree, so no behavior distinguishes the three graphs. -/
public theorem collision_arrowXY_arrowYX (σ : InterventionProfile (Fin 2)) :
    arrowXY.Δ g σ = arrowYX.Δ g σ := by
  rw [← collision_edgeless_arrowXY, collision_edgeless_arrowYX]

/-- **The collision at every rational weight function, first pair.** The
source's `σ` is a probability mixture of intervention patterns, not a single
pattern; agreement on deterministic patterns lifts to the atlas rational
simplex, and the linear theorem is stronger within `ℚ`. -/
public theorem collision_mix_edgeless_arrowXY (w : Mixture (Fin 2)) :
    edgeless.Δmix g w = arrowXY.Δmix g w :=
  Model.Δmix_congr _ _ _ _ collision_edgeless_arrowXY

/-- **The collision at every rational weight function, second pair.** -/
public theorem collision_mix_edgeless_arrowYX (w : Mixture (Fin 2)) :
    edgeless.Δmix g w = arrowYX.Δmix g w :=
  Model.Δmix_congr _ _ _ _ collision_edgeless_arrowYX

/-- **The collision at every rational weight function, third pair.** -/
public theorem collision_mix_arrowXY_arrowYX (w : Mixture (Fin 2)) :
    arrowXY.Δmix g w = arrowYX.Δmix g w :=
  Model.Δmix_congr _ _ _ _ collision_arrowXY_arrowYX

/--
**The shared transform is not degenerate.**

Under no intervention the common value is `1/2 - P(X=1, Y=1) = 1/2 - 1/2 · 4/5
= 1/10`, which is positive: the agent strictly prefers the action `1`. Without a
pinned value the collision theorems would also hold of a transform that is
identically zero, and would say nothing.
-/
public theorem transform_identity_edgeless :
    edgeless.Δ g (fun _ => LocalIntervention.identity) = 1/10 := by
  rw [Δ_eq_half_sub_joint]
  unfold Model.jointProb Model.factor
  simp [Fin.prod_univ_two, LocalIntervention.identity,
    identityIntervention, edgeless, bernoulli, asg]
  norm_num

/--
**The transform is negative somewhere**, so its sign data is not constant.

At `do(X=1)` with `Y` left alone, `Δ = 1/2 - 1 · (4/5) = -3/10`: the agent
strictly prefers the action `0`. Together with `transform_identity_edgeless`,
which is positive, this shows no single policy is optimal across all mixtures —
the *domain dependence* that (M3) exists to force, and an explicit hypothesis of
Richens and Everitt's theorem. Without it, nothing on record would place this
construction inside the null set that theorem excludes, which is the whole
reason a margin class is wanted.
-/
public theorem transform_doX1_edgeless :
    edgeless.Δ g (fun c => if c = X then LocalIntervention.fix true
                           else LocalIntervention.identity) = -(3/10) := by
  rw [Δ_eq_half_sub_joint]
  unfold Model.jointProb Model.factor
  simp [Fin.prod_univ_two, Fin.sum_univ_two, LocalIntervention.fix,
    LocalIntervention.identity, fixIntervention, identityIntervention,
    edgeless, bernoulli, asg]
  norm_num

/-- The transform takes both signs, so the sign data an agent reveals is not
constant across tasks. -/
public theorem transform_takes_both_signs :
    (∃ σ, 0 < edgeless.Δ g σ) ∧ (∃ σ, edgeless.Δ g σ < 0) :=
  ⟨⟨_, by rw [transform_identity_edgeless]; norm_num⟩,
   ⟨_, by rw [transform_doX1_edgeless]; norm_num⟩⟩

/-- The same value under `X → Y`, by the collision. -/
public theorem transform_identity_arrowXY :
    arrowXY.Δ g (fun _ => LocalIntervention.identity) = 1/10 := by
  rw [← collision_edgeless_arrowXY, transform_identity_edgeless]

/-- The same value under `Y → X`, by the collision. -/
public theorem transform_identity_arrowYX :
    arrowYX.Δ g (fun _ => LocalIntervention.identity) = 1/10 := by
  rw [← collision_edgeless_arrowYX, transform_identity_edgeless]

/-! ## The margin class

`MAIS-O23` quantifies over `M(s, λ)`, so a collision only bears on it once the
three models are shown to live there. Skeleton: `O = ∅`, `Z = {X, Y}`, utility
gap `g`, and margin `λ = 1/10`.
-/

/- A utility realizing the gap, with values in `[0,1]` as Definition 2.3 requires. -/
@[expose] public def u (d : Bool) (v : Assignment (Fin 2)) : ℚ :=
  if d then (1 + g v)/2 else (1 - g v)/2

/-- The utility takes values in `[0,1]`. -/
public theorem u_mem_unitInterval (d : Bool) (v : Assignment (Fin 2)) :
    0 ≤ u d v ∧ u d v ≤ 1 := by
  have h : g v = 1/2 ∨ g v = -(1/2) := by
    by_cases hv : v X = 1 ∧ v Y = 1
    · right
      simp [g, hv]
    · left
      simp [g, hv]
  cases d <;> rcases h with h | h <;> constructor <;> simp [u, h] <;> norm_num

/-- The utility realizes the gap: `g(z) = u(1,z) - u(0,z)`. -/
public theorem u_gap (v : Assignment (Fin 2)) : u true v - u false v = g v := by
  simp [u]; ring

/-- The skeleton of the construction: nothing observed, both variables scored. -/
@[expose] public def skel : Skeleton (Fin 2) where
  observed := ∅
  utilityParents := Finset.univ
  utility := u
  utility_parents := by
    intro d v w h
    have : v = w := funext fun c => h c (Finset.mem_univ c)
    rw [this]
  utility_mem_unitInterval := u_mem_unitInterval

/-- The gap computed from `skel` is the construction's named gap. -/
public theorem skel_gap : skel.gap = g := by
  funext v
  exact u_gap v

/-- The margin. -/
@[expose] public def lam : ℚ := 1/10

/-- `g` takes the value `1/2` off the corner `(1,1)` and `-1/2` on it, so `|g| = 1/2`. -/
public theorem abs_g (v : Assignment (Fin 2)) : |g v| = 1/2 := by
  by_cases hv : v X = 1 ∧ v Y = 1 <;> simp [g, hv]

/-- **(M2)** holds: the decision always matters, by a margin of `1/2`. -/
public theorem skel_M2 : skel.M2 lam := by
  intro v
  rw [skel_gap, abs_g]
  norm_num [lam]

/-- **(M3)** holds: with nothing observed the slice condition is that `g` takes
both signs, and it does. -/
public theorem skel_M3 : skel.M3 := by
  intro w
  refine ⟨asg false false, asg true true, ?_, ?_, ?_, ?_⟩
  · intro c hc; simp [skel] at hc
  · intro c hc; simp [skel] at hc
  · rw [skel_gap]
    norm_num [g, asg, binaryState]
  · rw [skel_gap]
    norm_num [g, asg, binaryState]

/-- **(M5)** holds for any model on this skeleton: the score reads every
variable, so every parent-closed superset of the utility parents is everything,
and nothing is observed, so something is hidden. -/
public theorem skel_M5 (M : Model (Fin 2)) : skel.M5 M := by
  constructor
  · intro t ht _
    refine Finset.univ_subset_iff.mp fun c _ => ht ?_
    simp [skel]
  · exact Finset.ssubset_univ_iff.mpr (by decide)

/-- **(M6)** holds: flipping either variable at `(1,1)` moves the gap by `1`. -/
public theorem skel_M6 : skel.M6 lam := by
  intro j _
  fin_cases j
  · refine ⟨asg true true, 0, 1, by decide, ?_⟩
    rw [skel_gap]
    norm_num [g, asg, binaryState, lam, Function.update]
  · refine ⟨asg true true, 0, 1, by decide, ?_⟩
    rw [skel_gap]
    norm_num [g, asg, binaryState, lam, Function.update]

/-- The margin lies in `(0, ½)`, where the class is defined. -/
public theorem lam_valid : Skeleton.ValidMargin lam := by
  constructor <;> norm_num [lam]

/-- **(M1)** holds for the edgeless model: entries are `1/2` and `4/5`. -/
public theorem edgeless_M1 : Skeleton.M1 edgeless lam := by
  intro c a v
  fin_cases c <;> fin_cases a <;> constructor <;>
    norm_num [edgeless, bernoulli, lam]

/-- **(M4)** holds vacuously for the edgeless model: it has no edges. -/
public theorem edgeless_M4 : Skeleton.M4 edgeless lam := by
  intro c p hp
  simp [edgeless] at hp

/-- **The edgeless model is in the margin class** at `λ = 1/10`. -/
public theorem edgeless_mem : skel.MarginClass edgeless lam :=
  ⟨lam_valid, edgeless_M1, skel_M2, skel_M3, edgeless_M4, skel_M5 _, skel_M6⟩

/-- **(M1)** holds for `X → Y`: entries are `1/2`, `4/5` and `1/5`. -/
public theorem arrowXY_M1 : Skeleton.M1 arrowXY lam := by
  intro c a v
  fin_cases c <;> fin_cases a <;> by_cases hv : v X = 1 <;>
    constructor <;> simp [arrowXY, bernoulli, hv, lam] <;> norm_num

/-- **(M4)** holds for `X → Y`: the single edge has strength `3/5`. -/
public theorem arrowXY_M4 : Skeleton.M4 arrowXY lam := by
  intro c p hp
  fin_cases c
  · simp [arrowXY] at hp
  · have hpX : p = X := by simpa [arrowXY] using hp
    subst p
    refine ⟨asg true true, 0, 1, 1, by decide, ?_⟩
    norm_num [arrowXY, bernoulli, asg, binaryState, lam, Function.update]

/-- **`X → Y` is in the margin class** at `λ = 1/10`. -/
public theorem arrowXY_mem : skel.MarginClass arrowXY lam :=
  ⟨lam_valid, arrowXY_M1, skel_M2, skel_M3, arrowXY_M4, skel_M5 _, skel_M6⟩

/-- **(M1)** holds for `Y → X`: entries are `4/5` and `1/2`. -/
public theorem arrowYX_M1 : Skeleton.M1 arrowYX lam := by
  intro c a v
  fin_cases c <;> fin_cases a <;> by_cases hv : v Y = 1 <;>
    constructor <;> simp [arrowYX, bernoulli, hv, lam] <;> norm_num

/-- **(M4)** holds for `Y → X`: the single edge has strength `3/10`. -/
public theorem arrowYX_M4 : Skeleton.M4 arrowYX lam := by
  intro c p hp
  fin_cases c
  · have hpY : p = Y := by simpa [arrowYX] using hp
    subst p
    refine ⟨asg true true, 0, 1, 1, by decide, ?_⟩
    norm_num [arrowYX, bernoulli, asg, binaryState, lam, Function.update]
  · simp [arrowYX] at hp

/-- **`Y → X` is in the margin class** at `λ = 1/10`. -/
public theorem arrowYX_mem : skel.MarginClass arrowYX lam :=
  ⟨lam_valid, arrowYX_M1, skel_M2, skel_M3, arrowYX_M4, skel_M5 _, skel_M6⟩

/-- The edgeless model and `X → Y` are genuinely different: their parent maps
differ, so the collision is between distinct models rather than between
renamings of one. -/
public theorem edgeless_ne_arrowXY : edgeless.parents ≠ arrowXY.parents := by
  intro h
  have hY := congrFun h Y
  simp [edgeless, arrowXY] at hY

/-- The edgeless model and `Y → X` are genuinely different. -/
public theorem edgeless_ne_arrowYX : edgeless.parents ≠ arrowYX.parents := by
  intro h
  have hX := congrFun h X
  simp [edgeless, arrowYX] at hX

/-- `X → Y` and `Y → X` are genuinely different. -/
public theorem arrowXY_ne_arrowYX : arrowXY.parents ≠ arrowYX.parents := by
  intro h
  have hY := congrFun h Y
  simp [arrowXY, arrowYX] at hY

/-!
## Graph shape on two variables

The agenda's §5 class `MM₂(λ)` is defined as the models carrying `G→` or `G←`,
so a claim about it needs the graph pinned, not merely non-empty.
-/

/--
**On two variables, a model with any edge carries exactly one of the two
arrows.**

Acyclicity does the work twice: no self-loops, and no two-cycle. So the parent
map of a model with an edge is `arrowXY`'s or `arrowYX`'s, and the four-step
inference a reader would otherwise have to make — no self-loop, no two-cycle,
tables in range by (M1), edge strength by (M4) — is in the kernel for the first
two steps.
-/
public theorem mm2_shape (M : Model (Fin 2)) (h : ∃ c p, p ∈ M.parents c) :
    M.parents = arrowXY.parents ∨ M.parents = arrowYX.parents := by
  obtain ⟨rank, hrank⟩ := M.acyclic
  have hno : ¬ (X ∈ M.parents Y ∧ Y ∈ M.parents X) := by
    rintro ⟨h1, h2⟩
    exact lt_irrefl _ (lt_trans (hrank Y X h1) (hrank X Y h2))
  have hXX : X ∉ M.parents X := M.notMem_parents_self X
  have hYY : Y ∉ M.parents Y := M.notMem_parents_self Y
  by_cases hXY : X ∈ M.parents Y
  · left
    have hYX : Y ∉ M.parents X := fun hh => hno ⟨hXY, hh⟩
    funext c
    fin_cases c <;> ext x <;> fin_cases x <;> simp_all [arrowXY, X, Y]
  · right
    have hYempty : ∀ x, x ∉ M.parents Y := by
      intro x
      fin_cases x
      · exact hXY
      · exact hYY
    obtain ⟨c, p, hp⟩ := h
    have hcX : c = X := by
      fin_cases c
      · rfl
      · exact absurd hp (hYempty p)
    subst hcX
    have hYX : Y ∈ M.parents X := by
      have : p ≠ X := fun e => hXX (e ▸ hp)
      have hpY : p = Y := by fin_cases p <;> simp_all
      exact hpY ▸ hp
    funext c
    fin_cases c <;> ext x <;> fin_cases x <;> simp_all [arrowYX, X, Y]

/-! ## The counterexample is a family, not a point

`arrowXY` fixes `P(Y=1 ∣ X=0) = 1/5`. Nothing forces that value: the transform
reads only the `(1,1)` cell, and `P(Y=1 ∣ X=0)` never enters it. So the whole
segment of models obtained by varying that one parameter collides with
`edgeless`, and the counterexample is positive-dimensional inside `M(s, λ)`.

This bears on MAIS-O24(c), which asks how large the excluded set is: at this
skeleton it contains a segment, not a tuned point.
-/

/-- `X → Y` with `P(Y=1 ∣ X=0) = b₀` left free. `arrowXY` is `b₀ = 1/5`. -/
@[expose] public def arrowXYb (b0 : ℚ) (hlo : 0 ≤ b0) (hhi : b0 ≤ 1) : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun c => if c = Y then {X} else ∅
  acyclic := ⟨fun c => if c = Y then 1 else 0, by decide⟩
  cpt := fun c a v ↦ bernoulli
    (if c = X then 1/2 else if v X = 1 then 4/5 else b0) a
  cpt_parents := by
    intro c a v w h
    fin_cases c
    · simp
    · have hX : v X = w X := h X (by simp)
      simp [hX]
  cpt_nonneg := by
    intro c a v
    fin_cases a <;> simp [bernoulli] <;> split_ifs <;> norm_num <;> linarith
  cpt_sum := by
    intro c v
    rw [Fin.sum_univ_two]
    simp [bernoulli]

/-- **(M1)** for the family: needs `b₀ ∈ [λ, 1-λ]`. -/
public theorem arrowXYb_M1 (b0 : ℚ) (hlo : 0 ≤ b0) (hhi : b0 ≤ 1)
    (h1 : 1/10 ≤ b0) (h2 : b0 ≤ 9/10) : Skeleton.M1 (arrowXYb b0 hlo hhi) lam := by
  intro c a v
  fin_cases c <;> fin_cases a <;> by_cases hv : v X = 1 <;>
    constructor <;> simp [arrowXYb, bernoulli, hv, lam] <;> linarith

/-- **(M4)** for the family: needs the edge to keep strength `≥ λ`, i.e.
`b₀ ≤ 7/10`. -/
public theorem arrowXYb_M4 (b0 : ℚ) (hlo : 0 ≤ b0) (hhi : b0 ≤ 1)
    (h : b0 ≤ 7/10) : Skeleton.M4 (arrowXYb b0 hlo hhi) lam := by
  intro c p hp
  fin_cases c
  · simp [arrowXYb] at hp
  · have hpX : p = X := by simpa [arrowXYb] using hp
    subst p
    refine ⟨asg true true, 0, 1, 1, by decide, ?_⟩
    simp [arrowXYb, bernoulli, asg, binaryState, lam, Function.update]
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **The whole segment collides with the edgeless model.** -/
public theorem collision_edgeless_arrowXYb (b0 : ℚ) (hlo : 0 ≤ b0) (hhi : b0 ≤ 1)
    (σ : InterventionProfile (Fin 2)) :
    edgeless.Δ g σ = (arrowXYb b0 hlo hhi).Δ g σ := by
  rw [Δ_eq_half_sub_joint, Δ_eq_half_sub_joint]
  congr 1

/--
**A positive-dimensional family of counterexamples.**

For every `b₀ ∈ [1/10, 7/10]` the model `arrowXYb b₀` is in the margin class,
has a different graph from `edgeless`, and shares its behavior. `arrowXY` is the
single point `b₀ = 1/5`.
-/
public theorem margin_class_not_identifiable_family
    (b0 : ℚ) (h1 : 1/10 ≤ b0) (h2 : b0 ≤ 7/10) :
    ∃ M : Model (Fin 2),
      skel.MarginClass M lam ∧ M.parents ≠ edgeless.parents ∧
      skel.BehaviorEq edgeless M := by
  have hlo : 0 ≤ b0 := by linarith
  have hhi : b0 ≤ 1 := by linarith
  refine ⟨arrowXYb b0 hlo hhi, ⟨lam_valid, arrowXYb_M1 b0 hlo hhi h1 (by linarith),
    skel_M2, skel_M3, arrowXYb_M4 b0 hlo hhi h2, skel_M5 _, skel_M6⟩, ?_, ?_⟩
  · intro h
    have hY := congrFun h Y
    simp [arrowXYb, edgeless] at hY
  · exact Skeleton.behaviorEq_of_observed_eq_empty rfl
      (fun mix => by
        rw [skel_gap]
        exact Model.Δmix_congr _ _ _ mix.1 (collision_edgeless_arrowXYb b0 hlo hhi))

/-! ## The relation has teeth

A collision theorem says nothing unless models of the class can *fail* to
collide. `transform_identity_edgeless` rules out one degeneracy — both
transforms identically zero — but not the one that would empty the headline:
`BehaviorEq` holding of every pair.
-/

/-- The edgeless model with `P(X=1) = 1/5` instead of `1/2`. Still in the margin
class; behaviorally distinguishable from `edgeless`. -/
@[expose] public def other : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun _ => ∅
  acyclic := ⟨fun _ => 0, by intro c p hp; simp at hp⟩
  cpt := fun c a _ ↦ bernoulli (if c = X then 1/5 else 4/5) a
  cpt_parents := by intro c a v w _; rfl
  cpt_nonneg := by
    intro c a v
    fin_cases a <;> simp [bernoulli] <;> split_ifs <;> norm_num
  cpt_sum := by
    intro c v
    rw [Fin.sum_univ_two]
    simp [bernoulli]

/-- `other` is in the margin class at `λ = 1/10`. -/
public theorem other_mem : skel.MarginClass other lam := by
  refine ⟨lam_valid, ?_, skel_M2, skel_M3, ?_, skel_M5 _, skel_M6⟩
  · intro c a v
    fin_cases c <;> fin_cases a <;> constructor <;>
      norm_num [other, bernoulli, lam]
  · intro c p hp
    simp [other] at hp

/-- The transform of `other` under no intervention: `1/2 - 1/5 · 4/5 = 17/50`. -/
public theorem transform_identity_other :
    other.Δ g (fun _ => LocalIntervention.identity) = 17/50 := by
  rw [Δ_eq_half_sub_joint]
  unfold Model.jointProb Model.factor
  simp [Fin.prod_univ_two, LocalIntervention.identity, identityIntervention,
    other, bernoulli, asg]
  norm_num

/--
**Behavioral equality is a real constraint on the margin class.**

`edgeless` and `other` are both in `M(s, λ)` and are told apart by behavior. So
the collision theorems below assert something: `BehaviorEq` is not a relation
that holds of every pair of models the class admits.
-/
public theorem behaviorEq_has_teeth : ¬ skel.BehaviorEq edgeless other := by
  intro h
  have hb := h ∅ (by simp [skel]) (asg false false)
    (ProbMixture.dirac (fun _ ↦ LocalIntervention.identity))
  rw [Model.Δmask_empty, Model.Δmask_empty, Model.Δmix_eq_sum,
    Model.Δmix_eq_sum] at hb
  have hpick : ∀ f : InterventionProfile (Fin 2) → ℚ,
      (∑ σ, (if σ = (fun _ => LocalIntervention.identity) then (1:ℚ) else 0) * f σ)
        = f (fun _ => LocalIntervention.identity) := by
    intro f
    rw [Finset.sum_eq_single (fun _ => LocalIntervention.identity)]
    · simp
    · intro b _ hb; simp [hb]
    · intro hp; simp at hp
  simp only [ProbMixture.dirac_apply] at hb
  rw [hpick, hpick, skel_gap, transform_identity_edgeless,
    transform_identity_other] at hb
  norm_num at hb

/-!
## The answer to MAIS-O23

Two distinct models of the margin class with one behavior.
-/

/--
**Margins do not imply behavioral identifiability.**

MAIS-O23 asks: fix a skeleton and `λ ∈ (0, ½)`; if `M, M' ∈ M(s, λ)` satisfy
`Δ_M = Δ_M'`, must `M = M'`? Here they need not: two models of the class at
`λ = 1/10`, distinct as graphs, whose transforms agree at every rational
probability mixture of local interventions.

The cancellation is the one the agenda said a counterexample would reveal: the
gap reads only the `(1,1)` cell, so marginals that differ are invisible to
behavior.
-/
public theorem margin_class_not_identifiable :
    Skeleton.ValidMargin lam ∧ ∃ M M' : Model (Fin 2),
      skel.MarginClass M lam ∧ skel.MarginClass M' lam ∧
      M.parents ≠ M'.parents ∧ M ≠ M' ∧
      skel.BehaviorEq M M' :=
  ⟨lam_valid, edgeless, arrowXY, edgeless_mem, arrowXY_mem,
    edgeless_ne_arrowXY, fun h => edgeless_ne_arrowXY (by rw [h]),
    Skeleton.behaviorEq_of_observed_eq_empty rfl (fun mix => by
      rw [skel_gap]
      exact collision_mix_edgeless_arrowXY mix.1)⟩

/--
**The same collision, on the source's literal real chart.**

`margin_class_not_identifiable` is checked on rational literals.
`Skeleton.marginClass_mapRat` and `Skeleton.behaviorEq_mapRat` carry both the
class membership and the whole behavioural family into the reals, so the printed
question is answered on its own chart rather than on a rational restriction of
it. The behavioural half is not a cast of the hypothesis: real mixtures are not
images of rational ones, and the transport goes through profile-wise agreement.
-/
public theorem margin_class_not_identifiable_real :
    Skeleton.ValidMargin ((lam : ℚ) : ℝ) ∧
      ∃ M M' : AISafetyAtlas.Causal.Model (Fin 2) (binaryDim (Fin 2)) ℝ,
      (skel.mapRat ℝ).MarginClass M ((lam : ℚ) : ℝ) ∧
      (skel.mapRat ℝ).MarginClass M' ((lam : ℚ) : ℝ) ∧
      M.parents ≠ M'.parents ∧ M ≠ M' ∧
      (skel.mapRat ℝ).BehaviorEq M M' := by
  obtain ⟨hlam, M, M', hM, hM', hp, hne, hbeh⟩ := margin_class_not_identifiable
  refine ⟨(Skeleton.marginClass_mapRat (𝕝 := ℝ) hM).1, M.mapRat ℝ, M'.mapRat ℝ,
    Skeleton.marginClass_mapRat hM, Skeleton.marginClass_mapRat hM', hp, ?_,
    Skeleton.behaviorEq_mapRat hbeh⟩
  intro hcon
  exact hp (congrArg
    (fun N : AISafetyAtlas.Causal.Model (Fin 2) (binaryDim (Fin 2)) ℝ ↦ N.parents) hcon)

/--
**The same, without the edgeless model.**

A reviewer who holds that the intended class carries a genuine graph — the
agenda's `MM₂(λ)` is defined that way, as the models with graph `G→` or `G←` —
still gets a counterexample. The graph shape is in the conclusion, via
`mm2_shape`, rather than left to the reader: each model's parent map is one of
the two arrows, they are different arrows, and (M1) and (M4) supply the
parameter range and edge strength that complete `MM₂(1/10)` membership.

This therefore also bears on **MAIS-O34(a)**, which asks for the two-variable
family whether a margin `λ > 0` alone suffices for identifiability. It does not.
-/
public theorem margin_class_not_identifiable_two_graphs :
    Skeleton.ValidMargin lam ∧ ∃ M M' : Model (Fin 2),
      skel.MarginClass M lam ∧ skel.MarginClass M' lam ∧
      M.parents ≠ M'.parents ∧ M ≠ M' ∧
      (M.parents = arrowXY.parents ∨ M.parents = arrowYX.parents) ∧
      (M'.parents = arrowXY.parents ∨ M'.parents = arrowYX.parents) ∧
      skel.BehaviorEq M M' :=
  ⟨lam_valid, arrowXY, arrowYX, arrowXY_mem, arrowYX_mem,
    arrowXY_ne_arrowYX, fun h => arrowXY_ne_arrowYX (by rw [h]),
    mm2_shape arrowXY ⟨Y, X, by simp [arrowXY]⟩,
    mm2_shape arrowYX ⟨X, Y, by simp [arrowYX]⟩,
    Skeleton.behaviorEq_of_observed_eq_empty rfl (fun mix => by
      rw [skel_gap]
      exact collision_mix_arrowXY_arrowYX mix.1)⟩

/-- **The same transport for the two-graph reading.** See
`margin_class_not_identifiable_real`; this is the `MM₂(λ)` reading, so it also
carries **MAIS-O34(a)**'s margin-sufficiency negative onto the real chart. -/
public theorem margin_class_not_identifiable_two_graphs_real :
    Skeleton.ValidMargin ((lam : ℚ) : ℝ) ∧
      ∃ M M' : AISafetyAtlas.Causal.Model (Fin 2) (binaryDim (Fin 2)) ℝ,
      (skel.mapRat ℝ).MarginClass M ((lam : ℚ) : ℝ) ∧
      (skel.mapRat ℝ).MarginClass M' ((lam : ℚ) : ℝ) ∧
      M.parents ≠ M'.parents ∧ M ≠ M' ∧
      (M.parents = arrowXY.parents ∨ M.parents = arrowYX.parents) ∧
      (M'.parents = arrowXY.parents ∨ M'.parents = arrowYX.parents) ∧
      (skel.mapRat ℝ).BehaviorEq M M' := by
  obtain ⟨hlam, M, M', hM, hM', hp, hne, hor, hor', hbeh⟩ :=
    margin_class_not_identifiable_two_graphs
  refine ⟨(Skeleton.marginClass_mapRat (𝕝 := ℝ) hM).1, M.mapRat ℝ, M'.mapRat ℝ,
    Skeleton.marginClass_mapRat hM, Skeleton.marginClass_mapRat hM', hp, ?_, hor, hor',
    Skeleton.behaviorEq_mapRat hbeh⟩
  intro hcon
  exact hp (congrArg
    (fun N : AISafetyAtlas.Causal.Model (Fin 2) (binaryDim (Fin 2)) ℝ ↦ N.parents) hcon)

/-! ## The witness satisfies `def:margin` as printed

`Skeleton.marginClass_iff_printed` proves the categorical six conditions collapse
to `def:margin`'s printed binary ones. Running it on the witness turns that from
a general claim into a checked one on the object MAIS-O23 is answered with: the
model this collision is built from is in the printed class, not merely in an
atlas class that resembles it.

The printed form is worth reading off. `PrintedM1` constrains `P(Cᵢ = 1 | pa)`,
which is what a binary table stores; `PrintedM4` compares the two parent
configurations that differ in the edge's source, at the child's `1`-cell; and
`PrintedM5` is `Anc(U) = 𝐂` together with `𝐎 ⊊ 𝐂`, with `Anc(U)` taken over
`𝐙 ∪ 𝐎` because `def:cid` gives `U` the parents `{D} ∪ 𝐙` and `D` the parents
`𝐎`. -/
public theorem edgeless_printed : skel.PrintedMarginClass edgeless lam :=
  (Skeleton.marginClass_iff_printed skel edgeless lam).mp edgeless_mem

/-- The one-edge witness too, so the collapse is checked on a model that
actually exercises (M4)'s edge-strength clause — on the edgeless graph that
clause is vacuous. -/
public theorem arrowXY_printed : skel.PrintedMarginClass arrowXY lam :=
  (Skeleton.marginClass_iff_printed skel arrowXY lam).mp arrowXY_mem

end AISafetyAtlas.Examples.Causal
