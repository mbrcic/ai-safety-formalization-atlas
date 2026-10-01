module

public import AISafetyAtlas.Sovereignty.Transfer
public import AISafetyAtlas.Examples.Sovereignty.Quantifiers

/-!
# A thinner threat, a logged implementation, and a refinement that is not one

Witnesses for the three transfer results, each chosen so the hypothesis it
inhabits is doing work.

`pinThreat` restricts the opponent of `bitMatch` to naming `true` and leaves
the principal unrestricted. `bitMatch_forcesWithin_pinThreat` is a guarantee
that exists only because the threat class was thinned, and
`bitMatch_not_forcesWithin_univ` is the same target failing when it is not. So
`P4` is not a statement about a class that never separates.

`logged` implements `decider` with an extra coordinate nobody reads.
`logged_simulates` is a simulation that is not the identity, and
`logged_forces` is the abstract guarantee arriving on the other side.

`pinnedForm true` is the counterexample print warns about: every outcome it
produces is one the abstract game could produce, and it simulates nothing,
because the abstract commitment that names `false` has no concrete
counterpart. Outcome-set inclusion is not refinement.

`rowDecides` against `colDecides` is the other separation, and it is the one
Alur, Henzinger, Kupferman and Vardi's Proposition 2 records: simulation is
**not monotone in the coalition**. The two games have the same outcome range,
so they simulate each other at the full coalition, where the alternation
collapses; at the coalition holding only the player who decides in the abstract
game and nothing in the concrete one, the simulation fails outright.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Transfer

open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Examples.Sovereignty.Quantifiers

/-! ## `P4`: a guarantee that exists only against a thinner threat -/

/-- Everyone is unrestricted. -/
@[expose] public def unrestricted : ∀ i : Bool, Set (bitMatch.strategy i) :=
  fun _ => Set.univ

/-- The opponent must name `true`; the principal is unrestricted. -/
@[expose] public def pinThreat : ∀ i : Bool, Set (bitMatch.strategy i)
  | false => Set.univ
  | true => {true}

/-- **Against the thinner threat the principal wins**, by naming the bit the
opponent is pinned to. -/
public theorem bitMatch_forcesWithin_pinThreat :
    ForcesWithin bitMatch {false} pinThreat ({true} : Set Bool) := by
  refine ⟨fun _ => true, fun i => ?_, fun s hC hT => ?_⟩
  · obtain ⟨j, hj⟩ := i
    obtain rfl : j = false := hj
    trivial
  · have h0 : s false = true := hC ⟨false, rfl⟩
    have h1 : s true = true := hT true
    simp [bitMatch, h0, h1]

/-- **And against the full threat it does not**, which is
`bitMatch_not_forces` in the availability vocabulary. -/
public theorem bitMatch_not_forcesWithin_univ :
    ¬ ForcesWithin bitMatch {false} unrestricted ({true} : Set Bool) := by
  intro h
  exact bitMatch_not_forces (forces_iff_forcesWithin_univ.mpr h)

/-- So `P4` separates: thinning the opponent's availability strictly increases
what the principal can force. -/
public theorem threat_monotonicity_is_strict :
    ForcesWithin bitMatch {false} pinThreat ({true} : Set Bool) ∧
      ¬ ForcesWithin bitMatch {false} unrestricted ({true} : Set Bool) :=
  ⟨bitMatch_forcesWithin_pinThreat, bitMatch_not_forcesWithin_univ⟩

/-! ## `P11`: an implementation that carries the guarantee -/

/-- The implementation: the principal names an outcome together with a log
entry nobody reads. -/
@[expose] public def logged : GameForm.{0, 0, 0} Bool (Bool × Bool) where
  strategy _ := Bool × Bool
  outcome s := s false

/-- **The implementation simulates the abstract game**, reading the outcome
through the first coordinate. The simulation is not the identity: the strategy
spaces and the outcome type both differ. -/
public theorem logged_simulates :
    Simulates decider logged {false} Prod.fst := by
  intro sC₀
  refine ⟨fun _ => (sC₀ ⟨false, rfl⟩, false), fun s hs => ?_⟩
  have h0 : s false = (sC₀ ⟨false, rfl⟩, false) := hs ⟨false, rfl⟩
  refine ⟨fun _ => sC₀ ⟨false, rfl⟩, ?_, ?_⟩
  · rintro ⟨j, hj⟩
    obtain rfl : j = false := hj
    rfl
  · show sC₀ ⟨false, rfl⟩ = (s false).1
    rw [h0]

/-- **So the abstract guarantee arrives.** -/
public theorem logged_forces :
    Forces logged {false} (Prod.fst ⁻¹' ({true} : Set Bool)) :=
  forces_of_simulates logged_simulates (principalDecides_forces_singleton true)

/-! ## Outcome-set inclusion is not refinement -/

/-- Every outcome the pinned game produces is one the abstract game could
produce. -/
public theorem pinned_outcomes_subset :
    Set.range (pinnedForm (true : Bool)).outcome ⊆ Set.range decider.outcome := by
  rintro _ ⟨s, rfl⟩
  exact ⟨fun _ => true, rfl⟩

/-- **And it still simulates nothing.** The abstract commitment that names
`false` has footprint `{false}`, and the pinned game's only outcome is `true`,
so no concrete commitment answers it. This is why `Simulates` quantifies over
abstract commitments rather than comparing outcome sets. -/
public theorem not_simulates_pinned :
    ¬ Simulates decider (pinnedForm (true : Bool)) {false} id := by
  intro h
  obtain ⟨sC₁, hsC₁⟩ := h (fun _ => false)
  obtain ⟨s, hs, heq⟩ := hsC₁ (fun _ => PUnit.unit) (fun _ => rfl)
  have h1 : s false = true := heq
  have h0 : s false = false := hs ⟨false, rfl⟩
  have hbad : (false : Bool) = true := h0.symm.trans h1
  exact Bool.noConfusion hbad

/-! ## Simulation is not monotone in the coalition -/

/-- The abstract game: the first player names the outcome. -/
@[expose] public def rowDecides : GameForm.{0, 0, 0} Bool Bool where
  strategy _ := Bool
  outcome s := s false

/-- The concrete game: the *other* player names it. -/
@[expose] public def colDecides : GameForm.{0, 0, 0} Bool Bool where
  strategy _ := Bool
  outcome s := s true

/-- **At the full coalition the concrete game refines the abstract one**, since
the two outcome ranges agree and the alternation has collapsed. -/
public theorem decides_simulates_univ :
    Simulates rowDecides colDecides Set.univ id := by
  rw [simulates_univ_iff]
  rintro x -
  exact ⟨fun _ => x, rfl⟩

/-- **And at a subcoalition it does not.** The player who decides in the
abstract game decides nothing in the concrete one, so the commitment naming
`true` has no concrete counterpart that survives every reply. Simulation is not
monotone in the coalition, which is Proposition 2 of Alur, Henzinger, Kupferman
and Vardi read at game forms. -/
public theorem decides_not_simulates_subset :
    ¬ Simulates rowDecides colDecides ({false} : Set Bool) id := by
  intro h
  obtain ⟨sC₁, hsC₁⟩ := h fun _ => show rowDecides.strategy _ from true
  obtain ⟨s₀, hs₀, hout⟩ :=
    hsC₁ (fun i => match i with
      | true => show colDecides.strategy true from false
      | false => sC₁ ⟨false, rfl⟩)
      (fun i => by
        obtain ⟨i, hi⟩ := i
        cases hi
        rfl)
  have h₀ : rowDecides.outcome s₀ = true := hs₀ ⟨false, rfl⟩
  have h₁ : id (colDecides.outcome (fun i => match i with
      | true => show colDecides.strategy true from false
      | false => sC₁ ⟨false, rfl⟩)) = false := rfl
  rw [h₀, h₁] at hout
  exact absurd hout (by simp)

/-! ## The rest of the transfer vocabulary, at these same witnesses

Each statement below is a general transfer lemma read at a game form this file
already built, so that its hypotheses are met rather than assumed.
-/

/-- Everyone unrestricted, at `decider`. -/
@[expose] public def deciderAll : ∀ i : Bool, Set (decider.strategy i) :=
  fun _ => Set.univ

/-- The opponent is pinned to `true`; the principal keeps everything. -/
@[expose] public def deciderPinned : ∀ i : Bool, Set (decider.strategy i)
  | false => Set.univ
  | true => {true}

/-- The principal decides, so it wins with everything available. -/
public theorem decider_forcesWithin_all :
    ForcesWithin decider {false} deciderAll ({true} : Set Bool) :=
  forces_iff_forcesWithin_univ.mp (principalDecides_forces_singleton true)

/-- **`A1`: thinning the opponent alone cannot lose a guarantee.** The
principal's own availability is untouched and the opponent's has shrunk, which
is exactly `mono_threat`'s pair of hypotheses. -/
public theorem decider_forcesWithin_pinned :
    ForcesWithin decider {false} deciderPinned ({true} : Set Bool) :=
  ForcesWithin.mono_threat
    (fun i hi => by
      obtain rfl : i = false := hi
      rfl)
    (fun i _ => Set.subset_univ _)
    decider_forcesWithin_all

/-- **`P10` at `decider` read through negation.** Power over `{true}` in the
negated game is power over its preimage in the original. -/
public theorem decider_forces_map_iff :
    Forces (decider.map (fun b ↦ !b)) {false} ({true} : Set Bool) ↔
      Forces decider {false} ((fun b ↦ !b) ⁻¹' ({true} : Set Bool)) :=
  forces_map_iff_forces_preimage

/-- The same correspondence read on the effectivity families. -/
public theorem decider_mem_effectivity_map_iff :
    ({true} : Set Bool) ∈ effectivity (decider.map (fun b ↦ !b)) {false} ↔
      (fun b ↦ !b) ⁻¹' ({true} : Set Bool) ∈ effectivity decider {false} :=
  mem_effectivity_map_iff

/-- The identity migration, at `logged`. -/
public theorem logged_simulates_refl :
    Simulates logged logged {false} id :=
  simulates_refl logged {false}

/-- **Migrations compose**: `decider` to `logged` and then `logged` to itself
is still a simulation, now along the composed reading. -/
public theorem logged_simulates_comp :
    Simulates decider logged {false} (Prod.fst ∘ id) :=
  Simulates.comp logged_simulates logged_simulates_refl

/-- **At the empty coalition the alternation collapses to outcome containment**,
read between `decider` and its logging implementation. -/
public theorem logged_simulates_empty_iff :
    Simulates decider logged (∅ : Set Bool) Prod.fst ↔
      Set.range (Prod.fst ∘ logged.outcome) ⊆ Set.range decider.outcome :=
  simulates_empty_iff

/-- A one-demand catalogue the principal meets. -/
public theorem decider_demandwise :
    Demandwise decider {false} ({({true} : Set Bool)} : Set (Set Bool)) := by
  rintro Φ hΦ
  obtain rfl : Φ = ({true} : Set Bool) := hΦ
  exact principalDecides_forces_singleton true

/-- **`A2`: the whole catalogue survives the migration**, one demand at a time,
carried by the same simulation that carried the single guarantee. -/
public theorem logged_demandwise :
    Demandwise logged {false}
      ((fun Φ ↦ Prod.fst ⁻¹' Φ) '' ({({true} : Set Bool)} : Set (Set Bool))) :=
  demandwise_of_simulates logged_simulates decider_demandwise

end AISafetyAtlas.Examples.Sovereignty.Transfer
