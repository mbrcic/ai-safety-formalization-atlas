module

public import AISafetyAtlas.Oversight.JointObservation.Architecture
public import AISafetyAtlas.Knowledge

/-!
# Joint observation — coverage and collision

## The definitional commitment

`Covers q h` says the hazard decision **factors through** the candidate's output:
there exists a rule on `q.Output` that reproduces `h` on every execution.

It is deliberately *not* defined as "no collision exists". Defining it that way
would collapse `covers_iff_no_collision` — the characterization this file exists to
prove — into definitional unfolding, and would leave the artifact with no statement
connecting an observation's *informational content* to a *usable decision rule*.

## Relation to the generic kernel

`Covers q h` is *definitionally* `AISafetyAtlas.Knowledge.Knowable q.observe h`:
the coalition-indexed statement here is that kernel at `Ω := A.Execution`,
`I := q.Output`, `Y := Bool`. `covers_iff_no_collision` is therefore
`Knowledge.knowable_iff_no_collision` applied to `q.observe`, and no bridge lemma
is needed — the kernel results apply to a `Covers` hypothesis directly.

The fibre argument lives once, in the kernel, where it is discharged by Mathlib's
`Function.factorsThrough_iff`: a decision rule is assembled from the hazard values
on each fibre of `observe`, well defined exactly when no fibre contains both a safe
and a hazardous execution. In that generic form it uses classical choice;
`FiniteDecision` supplies the constructive executable counterpart.

What stays here is what is genuinely coalition-specific: the `CollisionWitness`
certificate consumers cite, and the finite decision procedure.

A `CollisionWitness` is the concrete negative certificate: two executions the
candidate cannot tell apart, one safe and one hazardous.
-/

namespace AISafetyAtlas.Oversight.JointObservation

universe u v w

variable {A : EvidenceArchitecture.{u, v}}

/-! ## Coverage -/

/--
The candidate **covers** the hazard: the hazard decision factors through the
candidate's output.

Quantifier order is part of the freeze — one decision rule, uniform in the
execution. Swapping the quantifiers would give a vacuous per-execution statement.
-/
@[expose] public def Covers
    (q : CandidateObservation.{u, v, w} A)
    (h : Hazard A) : Prop :=
  ∃ decideHazard : q.Output → Bool, ∀ σ, h σ = decideHazard (q.observe σ)

/-! ## Collision -/

/--
A **collision witness**: two executions with the same observation but different
hazard status. This is the negative certificate a checker returns, and the object a
downstream consumer inspects to see *which* pair the current architecture cannot
separate.
-/
public structure CollisionWitness
    (q : CandidateObservation.{u, v, w} A)
    (h : Hazard A) where
  /-- One side of the indistinguishable pair. -/
  left : A.Execution
  /-- The other side. -/
  right : A.Execution
  /-- The candidate cannot tell them apart. -/
  sameObservation : q.observe left = q.observe right
  /-- Yet they differ in hazard status. -/
  hazardDiffers : h left ≠ h right

/-! ## C1 — the characterization -/

/--
**C1 — coverage/collision characterization.**

Factorization of the hazard through the candidate's output is equivalent to the
absence of any safe/hazardous pair colliding at that output.

This is the flagship statement of the kernel: it is what licenses reading a
collision witness as a genuine informational obstruction rather than a failure of
one particular decision rule.

The fibre argument is not repeated here. `Covers q h` is definitionally
`Knowledge.Knowable q.observe h`, so this is the generic characterization at
`Y := Bool`, whose `[Nonempty Y]` hypothesis is discharged automatically.
-/
public theorem covers_iff_no_collision
    (q : CandidateObservation.{u, v, w} A)
    (h : Hazard A) :
    Covers q h ↔ ∀ σ τ, q.observe σ = q.observe τ → h σ = h τ :=
  Knowledge.knowable_iff_no_collision q.observe h

/-- A collision witness refutes coverage. -/
public theorem not_covers_of_collisionWitness
    {q : CandidateObservation.{u, v, w} A}
    {h : Hazard A}
    (cw : CollisionWitness q h) : ¬ Covers q h := by
  intro hc
  exact cw.hazardDiffers
    ((covers_iff_no_collision q h).mp hc cw.left cw.right cw.sameObservation)

/--
Conversely, a failure of coverage yields a concrete colliding pair. Stated
existentially: the constructive witness-producing form is `decideCoverage` in
`FiniteDecision`.
-/
public theorem exists_collisionWitness_of_not_covers
    {q : CandidateObservation.{u, v, w} A}
    {h : Hazard A}
    (hnc : ¬ Covers q h) : Nonempty (CollisionWitness q h) := by
  classical
  by_contra hempty
  refine hnc ((covers_iff_no_collision q h).mpr ?_)
  intro σ τ hst
  by_contra hne
  exact hempty ⟨{ left := σ, right := τ, sameObservation := hst, hazardDiffers := hne }⟩

/-! ## Families -/

/--
No candidate in the family covers the hazard: the family is **blind** to it.

Stated over a `CandidateFamily` so that "every local monitor fails" is a single
result rather than one result per principal.
-/
@[expose] public def FamilyBlind
    (F : CandidateFamily.{u, v, _, w} A)
    (h : Hazard A) : Prop :=
  ∀ i : F.Index, ¬ Covers (F.candidate i) h

end AISafetyAtlas.Oversight.JointObservation
