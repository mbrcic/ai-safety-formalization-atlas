module

public import AISafetyAtlas.Oversight.JointObservation.Coverage
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Joint observation — certified finite decision

## What this provides

For finitely many executions and decidable equality of the candidate output, an
**executable** decision that returns either a proof of coverage or a concrete
`CollisionWitness`. The result type carries its own evidence, so soundness holds by
construction: a consumer that receives `.collision w` already holds the certificate
and never needs to trust the checker.

Completeness is the content of `decideCoverage_covered_iff`: the checker answers
`covered` exactly when coverage actually holds. Together with C1 this connects an
executable check to the factorization definition, which is what makes the artifact a
usable certificate rather than a `Decidable` instance.

## Why an explicit enumeration

The two jobs need different assumptions, and separating them is the point.

Deciding the *proposition* `Covers q h` needs only proposition-level finiteness:
`decidableCovers` takes `Fintype A.Execution` and nothing more.

*Returning a concrete collision witness* is a stronger requirement. The checker must
compute and hand back a specific pair, and a `Fintype`'s underlying `Multiset` fixes
no canonical order from which to select one, so selection there routes through choice
and the result neither compiles nor reduces. `decideCoverage` therefore takes an
`ExecutionEnum` — the executions listed, plus a completeness proof. For a concrete
architecture that is a literal, and it is exactly the data a reviewer wants to see.

`DecidableEq q.Output` compares candidate outputs. Both are assumptions of the
*checker*, deliberately not fields of `EvidenceArchitecture` or
`CandidateObservation`: an architecture should not have to commit to executable
equality merely to be stated.
-/

namespace AISafetyAtlas.Oversight.JointObservation

universe u v w

variable {A : EvidenceArchitecture.{u, v}}

/--
The certified result of checking one candidate against one hazard: either coverage
with its proof, or a concrete collision witness.

A dependent result type rather than a `Bool`: the point of the checker is to hand a
downstream consumer usable evidence in both branches.
-/
public inductive CoverageResult
    (q : CandidateObservation.{u, v, w} A)
    (h : Hazard A) where
  /-- The hazard decision factors through this candidate, with proof. -/
  | covers (proof : Covers q h)
  /-- The candidate confuses a safe and a hazardous execution, with witness. -/
  | collision (witness : CollisionWitness q h)

/-- Which branch the checker took. -/
@[expose] public def CoverageResult.covered
    {q : CandidateObservation.{u, v, w} A}
    {h : Hazard A} : CoverageResult q h → Bool
  | .covers _ => true
  | .collision _ => false

/--
**Soundness, in both branches.** A result reports coverage exactly when coverage
holds — for *any* result value, not just the checker's.

This is where the evidence carried by the constructors does its work: the `covers`
branch hands over the proof directly, and the `collision` branch is refuted by C1.
A consumer therefore never trusts the checker; it inspects what the checker returned.
-/
public theorem CoverageResult.covered_eq_true_iff
    {q : CandidateObservation.{u, v, w} A}
    {h : Hazard A}
    (r : CoverageResult q h) : r.covered = true ↔ Covers q h := by
  cases r with
  | covers proof => exact iff_of_true rfl proof
  | collision witness =>
      exact iff_of_false Bool.false_ne_true (not_covers_of_collisionWitness witness)

/--
An explicit finite enumeration of the executions: the finiteness the checker can
actually run on, as data rather than as a classical existence statement.
-/
public structure ExecutionEnum (A : EvidenceArchitecture.{u, v}) where
  /-- The executions, listed. Duplicates are harmless. -/
  toList : List A.Execution
  /-- Nothing is missing. -/
  complete : ∀ σ, σ ∈ toList

/--
**C2 — the certified finite decision.**

Executable: it searches the enumerated execution pairs and returns evidence in either
branch. No `native_decide`, no `@[implemented_by]` — the trusted path is the
kernel-checked term, and it reduces.
-/
@[expose] public def decideCoverage
    (E : ExecutionEnum A)
    (q : CandidateObservation.{u, v, w} A)
    (h : Hazard A) [DecidableEq q.Output] :
    CoverageResult q h :=
  let pairs : List (A.Execution × A.Execution) :=
    E.toList.flatMap fun σ => E.toList.map fun τ => (σ, τ)
  match hb : pairs.filter
      (fun p => decide (q.observe p.1 = q.observe p.2 ∧ h p.1 ≠ h p.2)) with
  | [] =>
      .covers <| by
        refine (covers_iff_no_collision q h).mpr fun σ τ hst => ?_
        by_contra hne
        have hpair : (σ, τ) ∈ pairs :=
          List.mem_flatMap.mpr
            ⟨σ, E.complete σ, List.mem_map.mpr ⟨τ, E.complete τ, rfl⟩⟩
        have hmem : (σ, τ) ∈ pairs.filter
            (fun p => decide (q.observe p.1 = q.observe p.2 ∧ h p.1 ≠ h p.2)) :=
          List.mem_filter.mpr ⟨hpair, by simp [hst, hne]⟩
        rw [hb] at hmem
        exact absurd hmem (List.not_mem_nil)
  | p :: _ =>
      have hp : q.observe p.1 = q.observe p.2 ∧ h p.1 ≠ h p.2 := by
        have hmem : p ∈ pairs.filter
            (fun p => decide (q.observe p.1 = q.observe p.2 ∧ h p.1 ≠ h p.2)) := by
          rw [hb]; exact List.mem_cons_self
        exact of_decide_eq_true (List.mem_filter.mp hmem).2
      .collision
        { left := p.1
          right := p.2
          sameObservation := hp.1
          hazardDiffers := hp.2 }

/--
**C2 specification — completeness.**

The checker reports coverage exactly when the factorization-based `Covers` holds.
Soundness is already carried by the constructors of `CoverageResult`; this is the
statement that the checker never reports a spurious collision.
-/
public theorem decideCoverage_covered_iff
    (E : ExecutionEnum A)
    (q : CandidateObservation.{u, v, w} A)
    (h : Hazard A) [DecidableEq q.Output] :
    (decideCoverage E q h).covered = true ↔ Covers q h :=
  CoverageResult.covered_eq_true_iff _

/--
Decidability of coverage in the finite case, straight from C1: no enumeration needed,
because deciding a proposition never has to produce a witness. Exposed for consumers
that only need the proposition.
-/
public instance decidableCovers
    [Fintype A.Execution]
    (q : CandidateObservation.{u, v, w} A)
    (h : Hazard A) [DecidableEq q.Output] :
    Decidable (Covers q h) :=
  decidable_of_iff _ (covers_iff_no_collision q h).symm

end AISafetyAtlas.Oversight.JointObservation
