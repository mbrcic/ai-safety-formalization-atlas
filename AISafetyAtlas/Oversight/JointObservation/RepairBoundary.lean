module

public import AISafetyAtlas.Oversight.JointObservation.Coverage

/-!
# Joint observation — the repair boundary

## The paired result (C3)

1. **Post-processing cannot repair a collision.** Any further computation applied to
   an unchanged observation inherits every collision the original had.
2. **Genuine refinement preserves coverage.** Strengthening an observation so that it
   determines the old one never loses a hazard that was already covered.

Neither half is deep alone; the first is close to a computation. The value is the
architectural conclusion they license together, and the fact that downstream
consumers can cite them instead of re-deriving them:

> More computation over unchanged interfaces cannot recover missing information.
> Repair must refine evidence access, admit an appropriate joint predicate, enlarge
> the coalition, or otherwise change the observation architecture. Doing so is safe
> in the sense that it cannot destroy coverage already established.

Applied to `emittedArchitectureCandidate`, part 1 upgrades "the tuple of declared
views fails" into "**arbitrary** computation over the complete existing interface
fails" — which is the architectural claim a consumer needs, and the reason the two
halves are stated together rather than left to be re-derived at each use site.
-/

namespace AISafetyAtlas.Oversight.JointObservation

universe u v w w'

variable {A : EvidenceArchitecture.{u, v}}

/-! ## Post-processing -/

/--
Post-process a candidate's output without changing what it may read: same coalition,
same computation, one further function applied.
-/
@[expose] public def CandidateObservation.postprocess
    (q : CandidateObservation.{u, v, w} A)
    {β : Type w'}
    (g : q.Output → β) : CandidateObservation.{u, v, w'} A where
  coalition := q.coalition
  Output := β
  joint := fun x => g (q.joint x)

/-- Post-processing acts on observations exactly as expected. -/
public theorem observe_postprocess
    (q : CandidateObservation.{u, v, w} A)
    {β : Type w'}
    (g : q.Output → β)
    (σ : A.Execution) :
    (q.postprocess g).observe σ = g (q.observe σ) :=
  rfl

/-- A collision survives any post-processing. Data, not a proposition: the same
colliding pair is transported, so a consumer keeps the concrete witness. -/
public def CollisionWitness.postprocess
    {q : CandidateObservation.{u, v, w} A}
    {h : Hazard A}
    (cw : CollisionWitness q h)
    {β : Type w'}
    (g : q.Output → β) : CollisionWitness (q.postprocess g) h where
  left := cw.left
  right := cw.right
  sameObservation := by
    rw [observe_postprocess, observe_postprocess, cw.sameObservation]
  hazardDiffers := cw.hazardDiffers

/--
**C3, part 1 — post-processing cannot repair a collision.**

If a candidate fails to cover the hazard, no computation over its unchanged output
covers it either.

This is `Knowledge.not_knowable_comp` at `Ω := A.Execution`: `Covers` is
definitionally `Knowledge.Knowable q.observe`, and `(q.postprocess g).observe` is
`g ∘ q.observe` by `rfl`. Constructive, and axiom-free, in the kernel.
-/
public theorem postprocess_cannot_repair_collision
    {q : CandidateObservation.{u, v, w} A}
    {h : Hazard A}
    (hnc : ¬ Covers q h)
    {β : Type w'}
    (g : q.Output → β) : ¬ Covers (q.postprocess g) h :=
  Knowledge.not_knowable_comp g hnc

/-! ## Refinement -/

/--
`Refines q' q` — the candidate `q'` is **at least as informative** as `q`: `q`'s
observation is recoverable from `q'`'s.

Direction is part of the freeze: the refined (stronger) candidate is the *first*
argument, and it is the one that determines the other.
-/
@[expose] public def Refines
    (q' : CandidateObservation.{u, v, w'} A)
    (q : CandidateObservation.{u, v, w} A) : Prop :=
  ∃ f : q'.Output → q.Output, ∀ σ, q.observe σ = f (q'.observe σ)

/-- Post-processing produces something the original refines. -/
public theorem refines_postprocess
    (q : CandidateObservation.{u, v, w} A)
    {β : Type w'}
    (g : q.Output → β) : Refines q (q.postprocess g) :=
  ⟨g, fun σ => observe_postprocess q g σ⟩

/--
**C3, part 2 — refinement preserves coverage.**

If `q` covers the hazard and `q'` is at least as informative as `q`, then `q'` covers
it too. Repair by refining evidence access is therefore monotone: it cannot lose a
guarantee already established.

This is `Knowledge.Knowable.mono`: `Refines q' q` is definitionally
`Knowledge.Determines q'.observe q.observe`. Both halves of C3 are therefore the
same generic monotonicity result, stated once in the kernel — part 1 is its
contrapositive at `finer := q.observe`.
-/
public theorem covers_of_refines
    {q' : CandidateObservation.{u, v, w'} A}
    {q : CandidateObservation.{u, v, w} A}
    {h : Hazard A}
    (hr : Refines q' q)
    (hc : Covers q h) : Covers q' h :=
  Knowledge.Knowable.mono hr hc

end AISafetyAtlas.Oversight.JointObservation
