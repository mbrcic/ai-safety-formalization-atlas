module

public import AISafetyAtlas.Causal.EffectiveGenericity
public import AISafetyAtlas.Examples.Causal.BehavioralCollision

/-!
# Worked model of MAIS-O24's certificate layer

`AISafetyAtlas.Causal.EffectiveGenericity` renders `prob:effective`'s polynomial
list and the class `𝕄(sk, λ, μ)` it cuts. This module runs both on the
two-variable skeleton, and checks the facts that decide whether the class is the
printed object rather than a shape with the right name:

* `S` really is the number of variables the polynomials range over, so the size
  bounds are bounds in the printed parameter;
* the list a solution supplies at a skeleton depends on the skeleton's **shape**
  and on nothing else — two skeletons that differ only in their numeric utility
  get the same list, which is the quantifier `prob:effective` fixes when it asks
  for a list *"for each diagram shape `(𝐂, 𝐎, 𝐙)`"*;
* both of conclusion (c)'s domains are the printed ones, and every object the
  problem quantifies over lands inside them;
* an **empty** list cuts nothing, so `𝕄(sk, λ, μ)` degenerates to `𝕄(sk, λ)`
  exactly when the certificate is vacuous. That degeneracy is the reason the
  atlas's earlier stand-in needed a hand-added properness clause, and it is not
  a defect of print's class — print's list comes from a solution, and a solution
  must satisfy conclusion (c), which an empty list cannot help with.
-/

namespace AISafetyAtlas.Examples.Causal.EffectiveGenericity

open AISafetyAtlas.Causal AISafetyAtlas.InformationTheory
open AISafetyAtlas.Examples.Causal

/-! ## `S` is the printed parameter -/

/-- `skel` reads its utility from both chance variables, so `dom(𝐙)` has four
elements and `S = K(G) + 4`. -/
public theorem o24Size_skel (G : Fin 2 → Finset (Fin 2)) :
    o24Size (skel.mapRat ℝ).utilityParents G = chartDim G + 4 := by
  simp [o24Size, skel]

/-- The `(θ, u)` variables number `K(G) + 2·2^{|𝐙|} = K(G) + 8`, where print's
`S` is `K(G) + 4`. The factor of two is invisible to a `poly(S)` requirement, and
`S` is a budget rather than a variable count. This used to read `S` counts the
variables the polynomials are written in — which was true only of the gap
coordinates that reading forced, and is retracted. What still makes
"polynomial in `S`" a bound in the printed parameter rather than in a convenient
recount of it. -/
public theorem card_o24Var_skel (G : Fin 2 → Finset (Fin 2)) :
    Fintype.card (O24Var (skel.mapRat ℝ).utilityParents G) = chartDim G + 8 := by
  rw [card_o24Var]
  simp [skel]

/-- At the edgeless graph `S = 2 + 4 = 6`: two free table entries and four
utility configurations. -/
public theorem o24Size_skel_edgeless :
    o24Size (skel.mapRat ℝ).utilityParents (fun _ ↦ ∅) = 6 := by
  rw [o24Size_skel]
  unfold chartDim
  simp

/-! ## The list cannot see the utility

`prob:effective` asks for a list *"for each diagram shape `(𝐂, 𝐎, 𝐙)` and each
compatible graph `G`"*, with `u` a **variable** of the polynomials. So a
solution's list is a function of the shape, and two skeletons sharing a shape
share a list however their utilities differ.

An earlier version of this module indexed the list by a whole `Skeleton`, which
carries the numeric utility, and so allowed exactly what print forbids: a
different certificate for each utility it was supposed to treat symbolically. -/

/-- A second skeleton on the same shape as `skel`, with a **different** utility:
`skel`'s gap is negated. Nothing about the shape changes. -/
public noncomputable def skelFlipped : Skeleton (Fin 2) (binaryDim (Fin 2)) Bool ℝ where
  observed := (skel.mapRat ℝ).observed
  utilityParents := (skel.mapRat ℝ).utilityParents
  utility := fun d v ↦ (skel.mapRat ℝ).utility (!d) v
  utility_parents := fun d v w h ↦ (skel.mapRat ℝ).utility_parents (!d) v w h
  utility_mem_unitInterval := fun d v ↦ (skel.mapRat ℝ).utility_mem_unitInterval (!d) v

/-- The flipped skeleton really does carry a different utility: its gap is the
negation of `skel`'s. So this is not a relabelling that the shape happens to
forget — it is a genuinely different member of the same shape. -/
public theorem skelFlipped_gap (v : Assignment (Fin 2) (binaryDim (Fin 2))) :
    skelFlipped.gap v = -(skel.mapRat ℝ).gap v := by
  simp only [Skeleton.gap, skelFlipped, Bool.not_true, Bool.not_false]
  ring

/-- **A solution's list is the same at both.** This is the quantifier repair
made visible: whatever certificate a solution supplies, it answers to
`(𝐎, 𝐙, G)` and cannot depend on the utility that its own polynomials take as an
argument. -/
public theorem o24List_indifferent_to_utility (Q : O24Assignment (Fin 2))
    (G : Fin 2 → Finset (Fin 2)) :
    HEq (Q.at (skel.mapRat ℝ) G) (Q.at skelFlipped G) :=
  HEq.rfl

/-! ## Conclusion (c)'s two domains

Print measures a set of `θ` and quantifies almost-every `u`, and both ranges are
bounded: table entries are probabilities, and `u : {0,1} × dom(𝐙) → [0,1]` makes
the gap coordinates lie in `[-1,1]`. Both bounds are load-bearing, but they fail
in *opposite* directions and it is worth being exact about which is which.

Dropping the `θ` bound makes (c) **weaker**: measured in all of `ℝ^{K(G)}` an
excluded set of infinite measure passes, since `(⊤ : ℝ≥0∞).toReal = 0`.

Dropping the `u` bound makes (c) **stronger**: `utilityBox` has positive measure,
so almost-everywhere on the ambient space implies almost-everywhere on the box, and the
unbounded form demands the estimate at utilities no skeleton realizes. That
admits fewer solutions than print's problem, so a downstream *"for every O24
solution, …"* would come out weaker than print. -/

/-- Every model on this skeleton presents its chart inside `chartBox`. -/
public theorem chartOn_mem_chartBox_skel (M : Model (Fin 2) (binaryDim (Fin 2)) ℝ)
    (G : Fin 2 → Finset (Fin 2)) : M.chartOn G ∈ chartBox G :=
  chartOn_mem_chartBox M G

/-- And both skeletons present their utility vector inside `utilityBox`, so
restricting (c)'s almost-every quantifier to the box discards no utility either
of them realizes. -/
public theorem utility_mem_utilityBox_skel :
    (fun dz : Bool × UtilityConfig (skel.mapRat ℝ).utilityParents ↦
      (skel.mapRat ℝ).utility dz.1 dz.2.extend) ∈
        utilityBox (skel.mapRat ℝ).utilityParents :=
  utility_mem_utilityBox _

public theorem utility_mem_utilityBox_skelFlipped :
    (fun dz : Bool × UtilityConfig skelFlipped.utilityParents ↦
      skelFlipped.utility dz.1 dz.2.extend) ∈
        utilityBox skelFlipped.utilityParents :=
  utility_mem_utilityBox _

/-! ## The empty certificate -/

/-- **An empty certificate cuts nothing.** With no polynomials the margin
condition `|Q_j| ≥ μ` is vacuous, so the class is the whole margin class at
every `μ`.

This is the degeneracy that forced the atlas's earlier rational stand-in to
carry a hand-added properness clause — an antecedent print does not have.
Against print's own class the degeneracy is harmless: a list this class comes
from is one supplied by a *solution*, and `prob:effective`(c) is a statement
about the list's own excluded set, which no empty list can discharge for a class
that is not already identifiable. -/
public theorem effectiveMarginClass_nil (lam mu : ℝ) :
    effectiveMarginClass (skel.mapRat ℝ) lam mu (fun _ _ _ ↦ []) =
      {M | (skel.mapRat ℝ).MarginClass M lam} := by
  ext M
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, nofun⟩

/-- The cut is monotone in the margin, on this skeleton as in general: a larger
`μ` keeps fewer models. -/
public theorem effectiveMarginClass_skel_mono (lam : ℝ) {mu nu : ℝ} (h : mu ≤ nu)
    (Q : O24Assignment (Fin 2)) :
    effectiveMarginClass (skel.mapRat ℝ) lam nu Q ⊆
      effectiveMarginClass (skel.mapRat ℝ) lam mu Q :=
  effectiveMarginClass_mono _ _ h _

/-! ## The bundle's fields bite

`O24Solution` is a predicate on a construction, and no inhabitant is expected —
`prob:effective` is an open problem. But a predicate can fail to have an
inhabitant for two very different reasons, and only one of them is acceptable
here. If the fields were jointly *contradictory*, then a downstream statement
reading *"for every O24 solution, …"* would be vacuously true, which is the
failure the O26 antecedent package must also rule out, and which is open on
that side too.

The check below is the cheap half of that: conclusion (a) is a real obstruction,
so the degenerate candidate — the assignment that supplies no polynomials at all
— is rejected by the bundle rather than accepted by it. That is evidence the
fields do work, not a claim that a solution exists. -/

/-- **The empty certificate is not a solution.** With no polynomials the cut is
the whole margin class, and MAIS-O23's collision lives there: two distinct
models with equal behaviour. So conclusion (a) fails.

This is the same fact from the other side of `effectiveMarginClass_nil`. It also
says why print's own class needs no properness clause: a list that cuts nothing
cannot satisfy (a) on a class that is not already identifiable. -/
public theorem not_o24Identifies_nil :
    ¬ O24Identifies (skel.mapRat ℝ) (fun _ _ _ ↦ []) := by
  intro h
  obtain ⟨hlam, M, M', hM, hM', -, hne, hbeh⟩ := margin_class_not_identifiable_real
  exact hne (h _ _ hlam hlam M ⟨hM, nofun⟩ M' ⟨hM', nofun⟩ hbeh)

/-! ## The variables are named, and the names are readable

The construction clause asks the machine to write polynomials in `(θ, u)`. What
makes that a statement about polynomials rather than about a string is that the
syntax names its variables and the naming is a **definition**: `encodeO24Var` is
fixed by the problem, not supplied by the solution.

The alternative the atlas carried until 2026-08-21 — syntax over `Fin S` plus a
solution-supplied bijection `O24Var Z G ≃ Fin S` — fails here. A bijection is an
encoding, and an unrestricted encoding is advice: it carries `log₂(S!)` bits of
per-instance choice about which coordinate each monomial is about, so a machine
emitting fixed syntax could "construct" a certificate it never computed. -/

/-- The name code is prefix-free on this skeleton's variables, so a concatenation
of names parses back and the whole output code is injective. -/
public theorem isPrefixCode_encodeO24Var_skel (G : Fin 2 → Finset (Fin 2)) :
    IsPrefixCode (encodeO24Var (skel.mapRat ℝ).utilityParents G) :=
  isPrefixCode_encodeO24Var _ _

/-- **The decision bit separates the two utility cells.** `u(1,z)` and `u(0,z)`
are distinct variables at the same configuration, and the code has to say which;
without this the decoder could read one as the other and a solution could name
`2^{|𝐙|}` coordinates while claiming `2·2^{|𝐙|}`. This is the regression the
`(θ,g) → (θ,u)` change makes possible, so it is checked rather than argued. -/
public theorem encodeO24Var_inr_ne_inr_of_decision_ne (G : Fin 2 → Finset (Fin 2))
    (v : UtilityConfig (skel.mapRat ℝ).utilityParents) :
    encodeO24Var (skel.mapRat ℝ).utilityParents G (.inr (true, v)) ≠
      encodeO24Var (skel.mapRat ℝ).utilityParents G (.inr (false, v)) := by
  intro h
  have := (isPrefixCode_encodeO24Var _ _).injective h
  simp at this

/-- A table coordinate and a utility coordinate never share a name: the leading
symbol says which kind of variable it is. Without this the decoder could read a
`θ` monomial as a `u` monomial. -/
public theorem encodeO24Var_inl_ne_inr (G : Fin 2 → Finset (Fin 2))
    (i : ChartIndex G) (v : Bool × UtilityConfig (skel.mapRat ℝ).utilityParents) :
    encodeO24Var (skel.mapRat ℝ).utilityParents G (.inl i) ≠
      encodeO24Var (skel.mapRat ℝ).utilityParents G (.inr v) := by
  intro h
  have := (isPrefixCode_encodeO24Var _ _).injective h
  simp at this

/-- **Names stay short.** `m ≤ S`, so a variable's name is `O(S)` symbols and a
`poly(S)`-monomial list still has a `poly(S)` transcript. Without this the
construction-time clause could be unsatisfiable for a reason having nothing to do
with the mathematics — the same failure a unary coefficient code would cause. -/
public theorem card_le_o24Size_skel (G : Fin 2 → Finset (Fin 2)) :
    2 ≤ o24Size (skel.mapRat ℝ).utilityParents G := by
  simpa using card_le_o24Size (C := Fin 2) (skel.mapRat ℝ).utilityParents G

end AISafetyAtlas.Examples.Causal.EffectiveGenericity
