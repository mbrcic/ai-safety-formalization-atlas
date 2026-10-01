module

public import AISafetyAtlas.Sovereignty.Service

/-!
# Two quantifier orders, and the conjunction that does not follow

Guaranteeing `A` and guaranteeing `B` is not guaranteeing `A ∩ B`, and
*"whatever you do, I have an answer"* is not *"I have an answer whatever you
do"*. Both failures are about where a quantifier sits, and both are stated here
because the repair for each is the same object: **one witness**.

## What is here

`ForcesResp` is the response-dependent quantifier: for every commitment by the
complement, *some* choice of the coalition lands the outcome in the target. It
is the proposal's `Can^resp`, and `forcesResp_of_forces` is the direction that
holds. The other direction fails, and the countermodel is in
`AISafetyAtlas.Examples.Sovereignty.Quantifiers`.

`forces_inter_of_shared_footprint` is the positive half of the conjunction
failure: two guarantees carried by **one** commitment do conjoin, because a
footprint inside `A` and inside `B` is a footprint inside `A ∩ B`. Two
guarantees carried by different commitments need not, and the countermodel is
in the same examples module.

`DemandwiseResp` and `demandwiseResp_of_demandwise` lift the same inclusion
from one target to a whole catalogue. That is the proposal's `S3`: reading a
catalogue with the response-dependent quantifier can only overestimate what a
principal can actually enforce, since a separate answer to each opponent
commitment is not a policy.

## Why the positive halves matter more than the separations

The proposal's `A6` says compositional assurance turns on a **shared witness**,
and gives `P7` as what goes wrong without one. Those are the same statement
read twice, and in this repository they are the same theorem:
`forces_inter_of_shared_footprint` is the composition rule, and the separation
is the remark that its hypothesis cannot be dropped.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

variable {N : Type u} {X : Type v} {G : GameForm.{u, v, w} N X}

/-! ## The response-dependent quantifier -/

/--
**Response-dependent capacity.** For every commitment by everyone outside `C`,
some commitment by `C` lands the outcome in `A`.

The quantifiers are the other way round from `Forces`, and the difference is
not cosmetic: a choice made after seeing the opponent's whole commitment is not
a strategy the coalition could have played.
-/
@[expose] public def ForcesResp (G : GameForm.{u, v, w} N X) (C : Set N)
    (A : Set X) : Prop :=
  ∀ sD : ∀ i : (Cᶜ : Set N), G.strategy i, ForcesGiven G Cᶜ sD C A

/-- **A uniform guarantee is a response-dependent one.** The same commitment
answers every opponent, so in particular it answers each one. -/
public theorem forcesResp_of_forces {C : Set N} {A : Set X} (h : Forces G C A) :
    ForcesResp G C A := by
  obtain ⟨sC, hsC⟩ := h
  exact fun _ => ⟨sC, fun s _ hC => hsC s hC⟩

/-- Response-dependent capacity is upward closed in the target, like `Forces`. -/
public theorem ForcesResp.mono {C : Set N} {A B : Set X} (h : ForcesResp G C A)
    (hAB : A ⊆ B) : ForcesResp G C B := by
  intro sD
  obtain ⟨sC, hsC⟩ := h sD
  exact ⟨sC, fun s hD hC => hAB (hsC s hD hC)⟩

/-! ## Conjunction, and the witness it needs -/

/--
**Two guarantees carried by one commitment do conjoin.**

This is the composition rule the proposal's `A6` names: assurance composes when
a single strategy discharges both obligations. The hypothesis is stated on the
footprint rather than on `Forces` precisely because that is what cannot be
recovered afterwards -- `Forces G C A` and `Forces G C B` each hide their own
witness, and nothing makes the two agree.
-/
public theorem forces_inter_of_shared_footprint {C : Set N} {A B : Set X}
    {sC : ∀ i : C, G.strategy i} (hA : outcomesOf G C sC ⊆ A)
    (hB : outcomesOf G C sC ⊆ B) : Forces G C (A ∩ B) :=
  forces_iff_outcomesOf_subset.mpr ⟨sC, Set.subset_inter hA hB⟩

/-- The same rule stated for a finite conjunction of any size, by intersecting
an arbitrary family the one commitment already secures. -/
public theorem forces_iInter_of_shared_footprint {C : Set N} {ι : Type*}
    {A : ι → Set X} {sC : ∀ i : C, G.strategy i}
    (h : ∀ j, outcomesOf G C sC ⊆ A j) : Forces G C (⋂ j, A j) :=
  forces_iff_outcomesOf_subset.mpr ⟨sC, Set.subset_iInter h⟩

/-! ## The same inclusion at a whole catalogue -/

/--
**Demandwise sovereignty read with the response-dependent quantifier.** Every
demand in the catalogue is met against each opponent commitment separately.
-/
@[expose] public def DemandwiseResp (G : GameForm.{u, v, w} N X) (C : Set N)
    (𝒬 : Set (Set X)) : Prop :=
  ∀ Φ ∈ 𝒬, ForcesResp G C Φ

/-- **The responsive reading overestimates sovereignty.** Every catalogue a
coalition genuinely enforces is one it enforces responsively; the converse
fails at a single demand, hence at a catalogue. This is the proposal's `S3`. -/
public theorem demandwiseResp_of_demandwise {C : Set N} {𝒬 : Set (Set X)}
    (h : Demandwise G C 𝒬) : DemandwiseResp G C 𝒬 :=
  fun Φ hΦ => forcesResp_of_forces (h Φ hΦ)

/-- And it is antitone in the catalogue, like `Demandwise`. -/
public theorem DemandwiseResp.mono {C : Set N} {𝒬 ℛ : Set (Set X)}
    (h : DemandwiseResp G C ℛ) (h𝒬 : 𝒬 ⊆ ℛ) : DemandwiseResp G C 𝒬 :=
  fun Φ hΦ => h Φ (h𝒬 hΦ)

end AISafetyAtlas.Sovereignty
