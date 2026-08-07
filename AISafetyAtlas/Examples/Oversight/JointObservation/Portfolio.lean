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

@[expose] public def bitC : Exec → Bool
  | .sigma000 | .sigma001 | .sigma010 | .sigma011 => false
  | .sigma100 | .sigma101 | .sigma110 | .sigma111 => true

@[expose] public def bitD : Exec → Bool
  | .sigma000 | .sigma001 | .sigma100 | .sigma101 => false
  | .sigma010 | .sigma011 | .sigma110 | .sigma111 => true

@[expose] public def bitE : Exec → Bool
  | .sigma000 | .sigma010 | .sigma100 | .sigma110 => false
  | .sigma001 | .sigma011 | .sigma101 | .sigma111 => true

@[expose] public def PrivateField : Principal → Type
  | .c | .d | .e => Bool

@[expose] public def EmittedView : Principal → Type
  | .c | .d | .e => Unit

@[expose] public def privateState : (i : Principal) → Exec → PrivateField i
  | .c, σ => bitC σ
  | .d, σ => bitD σ
  | .e, σ => bitE σ

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

public inductive HazardIx
  | cd
  | de
  deriving DecidableEq, Fintype

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

public inductive CandIx
  | cd
  | de
  | cde
  deriving DecidableEq, Fintype

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

public theorem qCD_cost : cost .cd = 3 := by decide
public theorem qDE_cost : cost .de = 3 := by decide
public theorem qCDE_cost : cost .cde = 7 := by decide

/-! ## Which candidate covers which hazard -/

public theorem qCD_covers_hCD : Covers qCD hCD :=
  ⟨id, by intro σ; cases σ <;> rfl⟩

public theorem qCD_not_covers_hDE : ¬ Covers qCD hDE :=
  not_covers_of_collisionWitness
    { left := .sigma000, right := .sigma001,
      sameObservation := rfl, hazardDiffers := by decide }

public theorem qDE_covers_hDE : Covers qDE hDE :=
  ⟨id, by intro σ; cases σ <;> rfl⟩

public theorem qDE_not_covers_hCD : ¬ Covers qDE hCD :=
  not_covers_of_collisionWitness
    { left := .sigma000, right := .sigma111,
      sameObservation := rfl, hazardDiffers := by decide }

public theorem qCDE_covers_hCD : Covers qCDE hCD :=
  ⟨fun o => o.1 && o.2.1, by intro σ; cases σ <;> rfl⟩

public theorem qCDE_covers_hDE : Covers qCDE hDE :=
  ⟨fun o => Bool.xor o.2.1 o.2.2, by intro σ; cases σ <;> rfl⟩

/-! ## The two covering portfolios -/

/-- Two narrow observations over different overlapping coalitions. -/
@[expose] public def kNarrow : Portfolio candidates := {.cd, .de}

/-- One broad grand-coalition observation. -/
@[expose] public def kBroad : Portfolio candidates := {.cde}

public theorem kNarrow_covers : PortfolioCovers candidates hazards kNarrow := by
  intro j
  cases j with
  | cd => exact ⟨.cd, by decide, qCD_covers_hCD⟩
  | de => exact ⟨.de, by decide, qDE_covers_hDE⟩

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

public theorem narrow_subsets_fail :
    ∀ K' ∈ ({CandIx.cd, CandIx.de} : Finset CandIx).powerset,
      K' ≠ ({CandIx.cd, CandIx.de} : Finset CandIx) →
        ¬ ((CandIx.cd ∈ K' ∨ CandIx.cde ∈ K') ∧
          (CandIx.de ∈ K' ∨ CandIx.cde ∈ K')) := by
  decide

public theorem kNarrow_inclusionMinimal :
    InclusionMinimalCovering candidates hazards kNarrow := by
  refine ⟨kNarrow_covers, fun K' hsub hcov => ?_⟩
  exact narrow_subsets_fail K' (Finset.mem_powerset.mpr hsub.1) (ne_of_lt hsub)
    ((portfolioCovers_iff K').mp hcov)

public theorem broad_subsets_fail :
    ∀ K' ∈ ({CandIx.cde} : Finset CandIx).powerset,
      K' ≠ ({CandIx.cde} : Finset CandIx) →
        ¬ ((CandIx.cd ∈ K' ∨ CandIx.cde ∈ K') ∧
          (CandIx.de ∈ K' ∨ CandIx.cde ∈ K')) := by
  decide

public theorem kBroad_inclusionMinimal :
    InclusionMinimalCovering candidates hazards kBroad := by
  refine ⟨kBroad_covers, fun K' hsub hcov => ?_⟩
  exact broad_subsets_fail K' (Finset.mem_powerset.mpr hsub.1) (ne_of_lt hsub)
    ((portfolioCovers_iff K').mp hcov)

/-! ## Declared cost-optimality -/

public theorem kNarrow_cost : PortfolioCost candidates cost kNarrow = 6 := by decide
public theorem kBroad_cost : PortfolioCost candidates cost kBroad = 7 := by decide

public theorem every_cover_costs_at_least_six :
    ∀ K' ∈ (Finset.univ : Finset CandIx).powerset,
      ((CandIx.cd ∈ K' ∨ CandIx.cde ∈ K') ∧
        (CandIx.de ∈ K' ∨ CandIx.cde ∈ K')) →
        6 ≤ ∑ i ∈ K', cost i := by
  decide

public theorem kNarrow_costOptimal :
    CostOptimalCovering candidates hazards cost kNarrow := by
  refine ⟨kNarrow_covers, fun K' hcov => ?_⟩
  rw [kNarrow_cost]
  exact every_cover_costs_at_least_six K'
    (Finset.mem_powerset.mpr (Finset.subset_univ K')) ((portfolioCovers_iff K').mp hcov)

public theorem kBroad_not_costOptimal :
    ¬ CostOptimalCovering candidates hazards cost kBroad := by
  intro h
  have hle := h.2 kNarrow kNarrow_covers
  rw [kBroad_cost, kNarrow_cost] at hle
  omega

end AISafetyAtlas.Examples.Oversight.JointObservation.Portfolio
