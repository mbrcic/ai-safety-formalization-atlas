module

public import AISafetyAtlas.Oversight.JointObservation
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# A three-principal portfolio instance where coalition choice matters

`Portfolio.lean` defines the verified target of bounded observation synthesis. This
second architecture exercises that target with two hazards whose cheaper narrow
observations use different overlapping coalitions:

```text
h_CD (sigma_abc) = a && b
h_DE (sigma_abc) = b xor c
```

Principals `C`, `D`, and `E` privately hold `a`, `b`, and `c`. The declared candidate
family contains:

| candidate | coalition | reports | declared cost |
|---|---|---|---:|
| `qCD` | `{C,D}` | `a && b` | 3 |
| `qDE` | `{D,E}` | `b xor c` | 3 |
| `qCDE` | `{C,D,E}` | `(a,b,c)` | 7 |

The narrow portfolio `{qCD,qDE}` and broad singleton `{qCDE}` both cover the hazard
family and are inclusion-minimal. Under the declared coordination-plus-disclosure cost,
only the narrow portfolio is cost-optimal. Agreement on every selected output implies
agreement on both hazards by the generic derived theorem
`portfolioCovers_implies_hazardEquivalent`.

This is checked target semantics, not a synthesizer. Candidates and costs are supplied;
nothing here generates a predicate, searches a mechanism library, validates the cost
model outside this instance, or establishes strategic production beyond truthful `M0`.
-/

namespace AISafetyAtlas.Examples.Oversight.JointObservation.Portfolio

open AISafetyAtlas.Oversight.JointObservation

/-! ## The three-principal, eight-execution architecture -/

/-- The three evidence-owning principals. -/
public inductive Principal
  | c
  | d
  | e
  deriving DecidableEq, Fintype

/-- Executions indexed by the private bits `(a,b,c)`. -/
public inductive Exec
  | sigma000
  | sigma001
  | sigma010
  | sigma011
  | sigma100
  | sigma101
  | sigma110
  | sigma111
  deriving DecidableEq, Fintype

/-- Bit `a` — the first index of `sigma_abc`, held privately by `C`. -/
@[expose] public def bitC : Exec → Bool
  | .sigma000 | .sigma001 | .sigma010 | .sigma011 => false
  | .sigma100 | .sigma101 | .sigma110 | .sigma111 => true

/-- Bit `b` — the second index, held privately by `D`. It is the one bit both
hazards depend on, which is why the two coalitions overlap. -/
@[expose] public def bitD : Exec → Bool
  | .sigma000 | .sigma001 | .sigma100 | .sigma101 => false
  | .sigma010 | .sigma011 | .sigma110 | .sigma111 => true

/-- Bit `c` — the third index, held privately by `E`. -/
@[expose] public def bitE : Exec → Bool
  | .sigma000 | .sigma010 | .sigma100 | .sigma110 => false
  | .sigma001 | .sigma011 | .sigma101 | .sigma111 => true

/-- Each principal privately holds one Boolean. -/
@[expose] public def PrivateField : Principal → Type
  | .c | .d | .e => Bool

/-- Every declared interface is `Unit`: the emitted views are **totally lossy**.
That is the point of the instance — coverage here can only come from coalition
observations, never from what principals disclose individually. -/
@[expose] public def EmittedView : Principal → Type
  | .c | .d | .e => Unit

/-- Who holds which bit: `C ↦ a`, `D ↦ b`, `E ↦ c`. -/
@[expose] public def privateState : (i : Principal) → Exec → PrivateField i
  | .c, σ => bitC σ
  | .d, σ => bitD σ
  | .e, σ => bitE σ

/-- The declared interface discards the private bit entirely. -/
@[expose] public def emit : (i : Principal) → PrivateField i → EmittedView i
  | .c, _ => ()
  | .d, _ => ()
  | .e, _ => ()

/-- A deliberately small architecture for exercising portfolio target semantics. -/
@[expose] public def arch : EvidenceArchitecture where
  Principal := Principal
  Execution := Exec
  PrivateField := PrivateField
  EmittedView := EmittedView
  privateState := privateState
  emit := emit

public instance : Fintype arch.Principal := inferInstanceAs (Fintype Principal)
public instance : DecidableEq arch.Principal := inferInstanceAs (DecidableEq Principal)
public instance : Fintype arch.Execution := inferInstanceAs (Fintype Exec)
public instance : DecidableEq arch.Execution := inferInstanceAs (DecidableEq Exec)

/-! ## Hazards -/

/-- The `C-D` conjunction hazard. -/
@[expose] public def hCD : Hazard arch := fun σ => bitC σ && bitD σ

/-- The `D-E` inconsistency hazard. -/
@[expose] public def hDE : Hazard arch := fun σ => Bool.xor (bitD σ) (bitE σ)

/-- Index for the two hazards the portfolio must cover. -/
public inductive HazardIx
  | cd
  | de
  deriving DecidableEq, Fintype

/-- The hazard family: both hazards at once, which is what makes coalition choice
non-trivial — no single *narrow* coalition covers both. -/
@[expose] public def hazards : HazardFamily arch where
  Index := HazardIx
  hazard
    | .cd => hCD
    | .de => hDE

/-! ## Coalition-indexed candidates -/

/-- The narrow `C-D` observation, computed only from `C` and `D` evidence. -/
@[expose] public def qCD : CandidateObservation arch where
  coalition := {.c, .d}
  Output := Bool
  joint := fun x => x ⟨.c, by simp⟩ && x ⟨.d, by simp⟩

/-- The narrow `D-E` observation, computed only from `D` and `E` evidence. -/
@[expose] public def qDE : CandidateObservation arch where
  coalition := {.d, .e}
  Output := Bool
  joint := fun x => Bool.xor (x ⟨.d, by simp⟩) (x ⟨.e, by simp⟩)

/-- The broad grand-coalition observation, disclosing all three private bits. -/
@[expose] public def qCDE : CandidateObservation arch where
  coalition := Finset.univ
  Output := Bool × Bool × Bool
  joint := fun x =>
    (x ⟨.c, Finset.mem_univ _⟩,
      x ⟨.d, Finset.mem_univ _⟩,
      x ⟨.e, Finset.mem_univ _⟩)

/-- Index for the three declared candidate observations. -/
public inductive CandIx
  | cd
  | de
  | cde
  deriving DecidableEq, Fintype

/-- The declared candidate family. **Supplied, not synthesized** — nothing here
searches a mechanism library or generates a predicate. -/
@[expose] public def candidates : CandidateFamily arch where
  Index := CandIx
  candidate
    | .cd => qCD
    | .de => qDE
    | .cde => qCDE

public instance : DecidableEq candidates.Index := inferInstanceAs (DecidableEq CandIx)
public instance : Fintype candidates.Index := inferInstanceAs (Fintype CandIx)

/-! ## Declared coordination-plus-disclosure cost -/

/-- Number of Boolean fields released by each supplied candidate. -/
@[expose] public def outputBits : CandIx → Nat
  | .cd | .de => 1
  | .cde => 3

/--
Declared instance cost `2 * (coalition size - 1) + output bits`.

This is an auditable proxy for cross-principal coordination plus disclosure, not a
universal scalarization of governance cost.
-/
@[expose] public def cost (i : CandIx) : Nat :=
  2 * ((candidates.candidate i).coalition.card - 1) + outputBits i

/-- `2 * (2 - 1) + 1 = 3`. -/
public theorem qCD_cost : cost .cd = 3 := by decide

/-- `2 * (2 - 1) + 1 = 3`. -/
public theorem qDE_cost : cost .de = 3 := by decide

/-- `2 * (3 - 1) + 3 = 7`. The grand coalition pays for both wider coordination
and wider disclosure, which is what separates the two portfolios below. -/
public theorem qCDE_cost : cost .cde = 7 := by decide

/-! ## Which candidate covers which hazard -/

/-- `qCD` reports `a && b`, which *is* the hazard: the decoder is `id`. -/
public theorem qCD_covers_hCD : Covers qCD hCD :=
  ⟨id, by intro σ; cases σ <;> rfl⟩

/-- `qCD` cannot see `h_DE`, and the reason is exhibited rather than asserted:
`sigma000` and `sigma001` differ only in `c`, which `{C,D}` never reads, yet
`b xor c` differs across them. -/
public theorem qCD_not_covers_hDE : ¬ Covers qCD hDE :=
  not_covers_of_collisionWitness
    { left := .sigma000, right := .sigma001,
      sameObservation := rfl, hazardDiffers := by decide }

/-- `qDE` reports `b xor c`, which *is* the hazard: the decoder is `id`. -/
public theorem qDE_covers_hDE : Covers qDE hDE :=
  ⟨id, by intro σ; cases σ <;> rfl⟩

/-- Symmetrically, `qDE` cannot see `h_CD`: `sigma000` and `sigma111` agree on
`b xor c` while disagreeing on `a && b`. -/
public theorem qDE_not_covers_hCD : ¬ Covers qDE hCD :=
  not_covers_of_collisionWitness
    { left := .sigma000, right := .sigma111,
      sameObservation := rfl, hazardDiffers := by decide }

/-- The grand coalition discloses all three bits, so `h_CD` is decoded from them. -/
public theorem qCDE_covers_hCD : Covers qCDE hCD :=
  ⟨fun o => o.1 && o.2.1, by intro σ; cases σ <;> rfl⟩

/-- And `h_DE` likewise. One candidate covering both is what makes the broad
portfolio a genuine competitor rather than a straw man. -/
public theorem qCDE_covers_hDE : Covers qCDE hDE :=
  ⟨fun o => Bool.xor o.2.1 o.2.2, by intro σ; cases σ <;> rfl⟩

/-! ## The two covering portfolios -/

/-- Two narrow observations over different overlapping coalitions. -/
@[expose] public def kNarrow : Portfolio candidates := {.cd, .de}

/-- One broad grand-coalition observation. -/
@[expose] public def kBroad : Portfolio candidates := {.cde}

/-- Two narrow observations cover both hazards — one each. -/
public theorem kNarrow_covers : PortfolioCovers candidates hazards kNarrow := by
  intro j
  cases j with
  | cd => exact ⟨.cd, by decide, qCD_covers_hCD⟩
  | de => exact ⟨.de, by decide, qDE_covers_hDE⟩

/-- One broad observation covers both hazards on its own. -/
public theorem kBroad_covers : PortfolioCovers candidates hazards kBroad := by
  intro j
  cases j with
  | cd => exact ⟨.cde, by decide, qCDE_covers_hCD⟩
  | de => exact ⟨.cde, by decide, qCDE_covers_hDE⟩

/-- The generic consequence instantiated for the narrow portfolio. -/
public theorem kNarrow_hazardEquivalent
    {x y : arch.Execution}
    (hSame : PortfolioIndistinguishable candidates kNarrow x y) :
    ∀ j : hazards.Index, hazards.hazard j x = hazards.hazard j y :=
  portfolioCovers_implies_hazardEquivalent kNarrow_covers hSame

/-- The generic consequence instantiated for the broad portfolio. -/
public theorem kBroad_hazardEquivalent
    {x y : arch.Execution}
    (hSame : PortfolioIndistinguishable candidates kBroad x y) :
    ∀ j : hazards.Index, hazards.hazard j x = hazards.hazard j y :=
  portfolioCovers_implies_hazardEquivalent kBroad_covers hSame

/-! ## Reducing portfolio coverage to finite membership -/

/--
**Coverage collapses to membership.** For this instance, a portfolio covers the
family exactly when it contains something that sees each hazard.

The right-hand side is a decidable proposition over three indices, which is what
lets the minimality and cost results below discharge by `decide` instead of
reasoning about arbitrary portfolios. The `not_covers` witnesses above are what
force the *only if* direction: without them, `qDE` could not be ruled out for
`h_CD`.
-/
public theorem portfolioCovers_iff (K : Portfolio candidates) :
    PortfolioCovers candidates hazards K ↔
      ((CandIx.cd ∈ K ∨ CandIx.cde ∈ K) ∧ (CandIx.de ∈ K ∨ CandIx.cde ∈ K)) := by
  constructor
  · intro h
    constructor
    · obtain ⟨i, hi, hcov⟩ := h .cd
      cases i with
      | cd => exact Or.inl hi
      | de => exact absurd hcov qDE_not_covers_hCD
      | cde => exact Or.inr hi
    · obtain ⟨i, hi, hcov⟩ := h .de
      cases i with
      | cd => exact absurd hcov qCD_not_covers_hDE
      | de => exact Or.inl hi
      | cde => exact Or.inr hi
  · rintro ⟨hcd, hde⟩ j
    cases j with
    | cd =>
        rcases hcd with h | h
        · exact ⟨.cd, h, qCD_covers_hCD⟩
        · exact ⟨.cde, h, qCDE_covers_hCD⟩
    | de =>
        rcases hde with h | h
        · exact ⟨.de, h, qDE_covers_hDE⟩
        · exact ⟨.cde, h, qCDE_covers_hDE⟩

/-! ## Inclusion-minimality -/

/-- Exhaustive check over the four subsets of `{cd, de}`: every proper one fails
the membership criterion. -/
public theorem narrow_subsets_fail :
    ∀ K' ∈ ({CandIx.cd, CandIx.de} : Finset CandIx).powerset,
      K' ≠ ({CandIx.cd, CandIx.de} : Finset CandIx) →
        ¬ ((CandIx.cd ∈ K' ∨ CandIx.cde ∈ K') ∧
          (CandIx.de ∈ K' ∨ CandIx.cde ∈ K')) := by
  decide

/-- Nothing can be dropped from the narrow portfolio. -/
public theorem kNarrow_inclusionMinimal :
    InclusionMinimalCovering candidates hazards kNarrow := by
  refine ⟨kNarrow_covers, fun K' hsub hcov => ?_⟩
  exact narrow_subsets_fail K' (Finset.mem_powerset.mpr hsub.1) (ne_of_lt hsub)
    ((portfolioCovers_iff K').mp hcov)

/-- The same check for `{cde}`: its only proper subset is empty, which covers
nothing. -/
public theorem broad_subsets_fail :
    ∀ K' ∈ ({CandIx.cde} : Finset CandIx).powerset,
      K' ≠ ({CandIx.cde} : Finset CandIx) →
        ¬ ((CandIx.cd ∈ K' ∨ CandIx.cde ∈ K') ∧
          (CandIx.de ∈ K' ∨ CandIx.cde ∈ K')) := by
  decide

/-- **Both** portfolios are inclusion-minimal. That is the point of computing it
for the broad one too: inclusion-minimality does not single out an arrangement,
so it cannot be the whole selection criterion. Cost is what separates them. -/
public theorem kBroad_inclusionMinimal :
    InclusionMinimalCovering candidates hazards kBroad := by
  refine ⟨kBroad_covers, fun K' hsub hcov => ?_⟩
  exact broad_subsets_fail K' (Finset.mem_powerset.mpr hsub.1) (ne_of_lt hsub)
    ((portfolioCovers_iff K').mp hcov)

/-! ## Declared cost-optimality -/

/-- `3 + 3 = 6`. -/
public theorem kNarrow_cost : PortfolioCost candidates cost kNarrow = 6 := by decide

/-- `7`, from the single grand-coalition candidate. -/
public theorem kBroad_cost : PortfolioCost candidates cost kBroad = 7 := by decide

/-- The lower bound, by exhaustion over all eight subsets of the candidate index:
no covering portfolio costs less than 6 under the declared cost. -/
public theorem every_cover_costs_at_least_six :
    ∀ K' ∈ (Finset.univ : Finset CandIx).powerset,
      ((CandIx.cd ∈ K' ∨ CandIx.cde ∈ K') ∧
        (CandIx.de ∈ K' ∨ CandIx.cde ∈ K')) →
        6 ≤ ∑ i ∈ K', cost i := by
  decide

/-- The narrow portfolio attains the bound, so it is cost-optimal **under this
declared cost**. Change the cost model and this result changes with it; nothing
here validates the model outside this instance. -/
public theorem kNarrow_costOptimal :
    CostOptimalCovering candidates hazards cost kNarrow := by
  refine ⟨kNarrow_covers, fun K' hcov => ?_⟩
  rw [kNarrow_cost]
  exact every_cover_costs_at_least_six K'
    (Finset.mem_powerset.mpr (Finset.subset_univ K')) ((portfolioCovers_iff K').mp hcov)

/-- And the broad one is not, at `7 > 6`. Together with the two minimality results
this is the instance's whole content: **coalition choice is a real decision**.
Both portfolios cover, both are inclusion-minimal, and only cost distinguishes
them — so an oversight arrangement cannot be selected on coverage alone. -/
public theorem kBroad_not_costOptimal :
    ¬ CostOptimalCovering candidates hazards cost kBroad := by
  intro h
  have hle := h.2 kNarrow kNarrow_covers
  rw [kBroad_cost, kNarrow_cost] at hle
  omega

end AISafetyAtlas.Examples.Oversight.JointObservation.Portfolio
