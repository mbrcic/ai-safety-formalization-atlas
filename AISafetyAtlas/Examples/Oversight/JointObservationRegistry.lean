module

public import AISafetyAtlas.Oversight.JointObservation.Registry
public import AISafetyAtlas.Oversight.JointObservation.Residual
public import AISafetyAtlas.Oversight.JointObservation.RepairBoundary
public import Mathlib.Data.Fintype.Prod

/-!
# A two-actor chain whose filings are informative and still insufficient

`AISafetyAtlas.Oversight.JointObservation.Registry` states both halves
conditionally, so this module inhabits them. The point of the witness is that
the registry here is **not** vacuous: each actor files a real fact about its own
component. It is simply coarser than the hazard needs, and that is enough.

## The setup

A supplier and a deployer, each holding an exact component version out of four.
The hazard is that the two components **do not match** — a relational property,
which is why no single actor can see it.

Each actor files one bit: whether its version is at least `2`. That is genuine
information, and it is what a registry schema with a version *band* would
collect.

* `chain_consortium_covers` — the two actors pooling their exact versions settle
  the hazard. Nothing is missing from the evidence.
* `chain_registry_blind` — the filings do not. Versions `(0, 0)` and `(0, 1)`
  file identically, and one is a match while the other is not.

Adding a third actor that also files a band changes nothing, which is what
`not_registry_covers_of_emit_collision` says for an arbitrary coalition. The
repair is a finer declared interface, not a longer chain.
-/

namespace AISafetyAtlas.Examples.Oversight.JointObservationRegistry

open AISafetyAtlas.Oversight.JointObservation

/-- Two actors: `false` is the supplier, `true` the deployer. -/
@[expose] public def chain : EvidenceArchitecture where
  Principal := Bool
  Execution := Fin 4 × Fin 4
  PrivateField := fun _ ↦ Fin 4
  EmittedView := fun _ ↦ Bool
  privateState := fun i σ ↦ if i then σ.2 else σ.1
  emit := fun _ v ↦ decide (2 ≤ (v : ℕ))

/-- `chain.Principal` is `Bool`, but it reaches instance synthesis as a structure
projection, so `Finset.univ` needs the instance named. The same obstruction is
why `chain_consortium_covers` reuses `mismatch` as its own decision rule rather
than writing a fresh `decide` over `chain.PrivateField`. -/
public instance : Fintype chain.Principal := inferInstanceAs (Fintype Bool)

/-- Same obstruction as `chain.Principal` above, for the execution type. -/
public instance : Fintype chain.Execution := inferInstanceAs (Fintype (Fin 4 × Fin 4))

/-- The whole chain. -/
@[expose] public def bothActors : Finset chain.Principal := Finset.univ

/-- `(consortiumCandidate chain bothActors).Output` reaches instance synthesis
as a structure projection too, so `DecidableEq` needs the instance named. -/
public instance : DecidableEq (consortiumCandidate chain bothActors).Output :=
  show DecidableEq ((i : {p // p ∈ bothActors}) → Fin 4) by infer_instance

/-- Same, at the identity post-processing used below. -/
public instance : DecidableEq ((consortiumCandidate chain bothActors).postprocess
    (id : (consortiumCandidate chain bothActors).Output →
      (consortiumCandidate chain bothActors).Output)).Output :=
  show DecidableEq ((i : {p // p ∈ bothActors}) → Fin 4) by infer_instance

/-- The hazard: the two components do not match. Relational, so no single actor
can see it however much it discloses. -/
@[expose] public def mismatch : Hazard chain :=
  fun σ ↦ decide (σ.1 ≠ σ.2)

/-- **The evidence settles the hazard.** Pooling the two exact versions decides
whether they match, so nothing is missing from what the actors hold. -/
public theorem chain_consortium_covers :
    Covers (consortiumCandidate chain bothActors) mismatch :=
  ⟨fun held ↦ mismatch (held ⟨false, Finset.mem_univ _⟩,
      held ⟨true, Finset.mem_univ _⟩),
    fun _ ↦ rfl⟩

/-- The registry's whole evidence on an execution is the tuple of filed bands
and nothing else -- `registryCandidate_observe` at this chain. Everything below
is a statement about that tuple. -/
public theorem chain_filing (σ : chain.Execution) :
    (registryCandidate chain bothActors).observe σ =
      fun i : {p // p ∈ bothActors} ↦ chain.emit i.1 (chain.privateState i.1 σ) :=
  registryCandidate_observe bothActors σ

/-- And the consortium's evidence is the tuple of exact versions --
`consortiumCandidate_observe` at this chain. The two theorems above are the whole
difference between the halves: same actors, same executions, different interface.
-/
public theorem chain_evidence (σ : chain.Execution) :
    (consortiumCandidate chain bothActors).observe σ =
      fun i : {p // p ∈ bothActors} ↦ chain.privateState i.1 σ :=
  consortiumCandidate_observe bothActors σ

/-- Both actors file the same band on these two executions: version `0` and
version `1` are both below `2`. -/
public theorem chain_files_agree (i : {p // p ∈ bothActors}) :
    chain.emit i.1 (chain.privateState i.1 ((0 : Fin 4), (0 : Fin 4)))
      = chain.emit i.1 (chain.privateState i.1 ((0 : Fin 4), (1 : Fin 4))) := by
  obtain ⟨i, -⟩ := i
  cases i <;> rfl

/-- And the hazard differs: `(0, 0)` matches, `(0, 1)` does not. -/
public theorem chain_hazard_differs :
    mismatch ((0 : Fin 4), (0 : Fin 4)) ≠ mismatch ((0 : Fin 4), (1 : Fin 4)) := by
  decide

/-- **The registry is blind to it.** -/
public theorem chain_registry_blind :
    ¬ Covers (registryCandidate chain bothActors) mismatch :=
  not_registry_covers_of_emit_collision chain_files_agree chain_hazard_differs

/-- **Open Problem 60 at a witness.** The evidence is sufficient and the filings
are not, so the diagnosis is the interface and not the length of the chain. -/
public theorem chain_consortium_covers_and_registry_does_not :
    Covers (consortiumCandidate chain bothActors) mismatch ∧
      ¬ Covers (registryCandidate chain bothActors) mismatch :=
  consortium_covers_and_registry_does_not chain_consortium_covers
    chain_files_agree chain_hazard_differs

/-- And the containment runs the way the module says: had the registry covered
the hazard, the evidence behind it would have too. -/
public theorem chain_consortium_covers_of_registry_covers :
    Covers (registryCandidate chain bothActors) mismatch →
      Covers (consortiumCandidate chain bothActors) mismatch :=
  consortium_covers_of_registry_covers

/-! ## C5's quantitative form and C3's boundary, at the same witness -/

/-- **Coverage, quantitatively, at the consortium.** Worst-case residual at
most one is exactly what `chain_consortium_covers` already established. -/
public theorem chain_covers_iff_worstResidual_le_one :
    Covers (consortiumCandidate chain bothActors) mismatch ↔
      worstResidual (consortiumCandidate chain bothActors) mismatch ≤ 1 :=
  covers_iff_worstResidual_le_one (consortiumCandidate chain bothActors) mismatch

/-- The per-output form of the same equivalence. -/
public theorem chain_covers_iff_residual_le_one :
    Covers (consortiumCandidate chain bothActors) mismatch ↔
      ∀ o, residual (consortiumCandidate chain bothActors) mismatch o ≤ 1 :=
  covers_iff_residual_le_one (consortiumCandidate chain bothActors) mismatch

/-- **Post-processing never lowers the residual**, at the identity
post-processing of the consortium candidate. -/
public theorem chain_worstResidual_le_postprocess :
    worstResidual (consortiumCandidate chain bothActors) mismatch
      ≤ worstResidual ((consortiumCandidate chain bothActors).postprocess
          (id : (consortiumCandidate chain bothActors).Output → _)) mismatch :=
  worstResidual_le_postprocess (consortiumCandidate chain bothActors) mismatch id

/-- The consortium candidate trivially refines itself. -/
public theorem chain_consortium_refines_self :
    Refines (consortiumCandidate chain bothActors) (consortiumCandidate chain bothActors) :=
  ⟨id, fun _ => rfl⟩

/-- **C3, part 2, at the consortium** — refinement (here, the reflexive case)
preserves the coverage `chain_consortium_covers` already established. -/
public theorem chain_covers_of_refines :
    Covers (consortiumCandidate chain bothActors) mismatch :=
  covers_of_refines chain_consortium_refines_self chain_consortium_covers

/-- **Post-processing produces something the original refines**, at the
identity post-processing of the consortium candidate. -/
public theorem chain_refines_postprocess :
    Refines (consortiumCandidate chain bothActors)
      ((consortiumCandidate chain bothActors).postprocess
        (id : (consortiumCandidate chain bothActors).Output → _)) :=
  refines_postprocess (consortiumCandidate chain bothActors) id

/-- **A failure of coverage yields a concrete colliding pair**, at the
registry's blindness to the mismatch hazard. -/
public theorem chain_exists_collisionWitness_of_not_covers :
    Nonempty (CollisionWitness (registryCandidate chain bothActors) mismatch) :=
  exists_collisionWitness_of_not_covers chain_registry_blind

/-- **`observe` is truthful reporting and nothing more**, at the consortium
candidate and an arbitrary execution. -/
public theorem chain_observe_truthful (σ : chain.Execution) :
    (consortiumCandidate chain bothActors).observe σ =
      (consortiumCandidate chain bothActors).joint
        (fun i => chain.privateState i.1 σ) :=
  observe_truthful (consortiumCandidate chain bothActors) σ

end AISafetyAtlas.Examples.Oversight.JointObservationRegistry
