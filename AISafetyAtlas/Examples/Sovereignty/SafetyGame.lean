module

public import AISafetyAtlas.Sovereignty.SafetyGame

/-!
# One system that can be held and one that cannot

Two states, `true` safe and `false` not. The controller names the next state;
the adversary either lets that stand or does not.

`holdable` is the system where the controller's action is the next state
outright. `true_mem_safetyKernel` shows the safe state is in the kernel, by
exhibiting the invariant set and its closure -- which is the whole content of a
safety certificate.

`losable` is the same shape with the adversary able to veto. `safetyKernel_empty`
shows its kernel is empty and `no_maintaining_strategy` reads that back through
`D1` as: no controller holds the safe state, positional or otherwise.

`false_mem_recovery` and `recovers_within_one` run `D2` on `holdable` with
everything viable: from the unsafe state the rank-decreasing controller reaches
the safe state in one step against every adversary. `no_recovering_controller`
runs the converse on `losable`, where the recovery sets never grow: no
controller reaches the safe state within any budget, not even one that
remembers every veto it has seen.
-/

namespace AISafetyAtlas.Examples.Sovereignty.SafetyGame

open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Sovereignty.SafetyGame

/-- The controller names the next state. -/
@[expose] public def holdable : SafetyGame Bool Bool Bool where
  step _ a _ := a

/-- The controller names the next state and the adversary may veto it. -/
@[expose] public def losable : SafetyGame Bool Bool Bool where
  step _ a b := a && !b

/-! ## A system that can be held -/

/-- **The safe state is in the kernel**, certified by the invariant set
`{true}` and one action at it. -/
public theorem true_mem_safetyKernel :
    (true : Bool) ∈ holdable.safetyKernel ({true} : Set Bool) := by
  refine holdable.subset_safetyKernel (W := ({true} : Set Bool)) le_rfl ?_ rfl
  rintro s rfl
  exact ⟨true, fun _ => rfl⟩

/-- **So some controller holds it forever**, by `D1`. -/
public theorem exists_maintaining :
    ∃ σ : Bool → Bool, holdable.Maintains σ ({true} : Set Bool) true :=
  (holdable.mem_safetyKernel_iff_exists_maintaining ({true} : Set Bool) true).mp
    true_mem_safetyKernel

/-! ## A system that cannot -/

/-- **The kernel is empty** when the adversary can veto: any state in it would
need an action surviving the veto, and none does. -/
public theorem safetyKernel_empty :
    losable.safetyKernel ({true} : Set Bool) = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hs
  obtain ⟨a, ha⟩ := losable.safetyKernel_subset_cpre ({true} : Set Bool) hs
  have hmem := losable.safetyKernel_subset ({true} : Set Bool) (ha true)
  have : losable.step s a true = false := by simp [losable]
  rw [this] at hmem
  exact Bool.noConfusion hmem

/-- **So no controller holds it**, by `D1` read the other way. -/
public theorem no_maintaining_strategy :
    ¬ ∃ σ : Bool → Bool, losable.Maintains σ ({true} : Set Bool) true := by
  intro h
  have := (losable.mem_safetyKernel_iff_exists_maintaining
    ({true} : Set Bool) true).mpr h
  rw [safetyKernel_empty] at this
  exact this

/-! ## Recovery within one step -/

/-- **The unsafe state is recoverable within one step**, with everything
viable. -/
public theorem false_mem_recovery :
    (false : Bool) ∈ holdable.recovery Set.univ ({true} : Set Bool) 1 :=
  Or.inr ⟨trivial, ⟨true, fun _ => rfl⟩⟩

/-- **And the rank-decreasing controller gets there**, by `D2`: against every
adversary the safe state is reached within one step, and everything on the way
is viable. -/
public theorem recovers_within_one (β : ℕ → Bool) :
    ∃ k ≤ 1,
      holdable.play (holdable.recoveryStrategy Set.univ ({true} : Set Bool))
        false β k ∈ ({true} : Set Bool) ∧
      ∀ j < k, holdable.play (holdable.recoveryStrategy Set.univ
        ({true} : Set Bool)) false β j ∈ (Set.univ : Set Bool) :=
  holdable.recovery_reaches Set.univ ({true} : Set Bool) 1 false
    ⟨1, false_mem_recovery⟩ (holdable.recoveryRank_le false_mem_recovery) β

/-! ## Nothing recovers the vetoed system -/

/-- **The recovery sets of `losable` never grow.** The adversary's veto sends
every action to `false`, so no state has a controllable predecessor into the
safe set. -/
public theorem losable_recovery (H : ℕ) :
    losable.recovery Set.univ ({true} : Set Bool) H = ({true} : Set Bool) := by
  induction H with
  | zero => rfl
  | succ k ih =>
      have hcpre : losable.cpre ({true} : Set Bool) = (∅ : Set Bool) := by
        ext s
        simp only [SafetyGame.cpre, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false, not_exists]
        intro a ha
        have := ha true
        simp [losable] at this
      show losable.recovery Set.univ ({true} : Set Bool) k ∪
          (Set.univ ∩ losable.cpre
            (losable.recovery Set.univ ({true} : Set Bool) k)) = _
      rw [ih, hcpre]
      simp

/-- **So no controller recovers it**, by the converse direction of `D2`.
The quantifier is over controllers that read the whole history of vetoes, so
this rules out memory as well as positional play. -/
public theorem no_recovering_controller (H : ℕ) :
    ¬ ∃ σ : Bool → List Bool → Bool, ∀ β : ℕ → Bool, ∃ k ≤ H,
      (losable.playH σ false β k).1 ∈ ({true} : Set Bool) ∧
      ∀ j < k, (losable.playH σ false β j).1 ∈ (Set.univ : Set Bool) := by
  rintro ⟨σ, hσ⟩
  have hmem :=
    losable.mem_recovery_of_recovers Set.univ ({true} : Set Bool) H σ false hσ
  rw [losable_recovery] at hmem
  simp at hmem

/-! ## Every safety-game lemma, applied

`AISafetyAtlas.Sovereignty.SafetyGame` proves eight results that nothing
instantiated. Each is applied below on `holdable`, the game whose kernel is
non-empty. The stream and play lemmas are unfoldings; `maintains_prodGame`
is applied at `holdable` against itself, which is the only pair this file has.
-/

/-- The prepended stream reads back, at zero and at a successor. -/
public theorem safety_consStream_readings (b : Bool) (β : ℕ → Bool) (n : ℕ) :
    consStream b β 0 = b ∧ consStream b β (n + 1) = β n :=
  ⟨consStream_zero b β, consStream_succ b β n⟩

/-- Both plays start where they were told to. -/
public theorem safety_play_zero (σ : Bool → Bool) (σH : Bool → List Bool → Bool)
    (s₀ : Bool) (β : ℕ → Bool) :
    holdable.play σ s₀ β 0 = s₀ ∧ holdable.playH σH s₀ β 0 = (s₀, []) :=
  ⟨holdable.play_zero σ s₀ β, holdable.playH_zero σH s₀ β⟩

/-- **A maintained product.** Two systems each holding their own invariant hold
the product invariant in the product game; applied at `holdable` against itself,
which is the only pair available here. -/
public theorem safety_maintains_prodGame :
    ∃ σ : Bool × Bool → Bool × Bool,
      (holdable.prodGame holdable).Maintains σ
        (({true} : Set Bool) ×ˢ ({true} : Set Bool)) (true, true) := by
  obtain ⟨σ, hσ⟩ := exists_maintaining
  exact ⟨fun s => (σ s.1, σ s.2), maintains_prodGame holdable holdable hσ hσ⟩

/-- Recovery is monotone in the viability set, and its membership unfolds to the
explicit controller-and-horizon statement. -/
public theorem safety_recovery_readings :
    holdable.recovery ({true} : Set Bool) ({true} : Set Bool) 1
        ⊆ holdable.recovery Set.univ ({true} : Set Bool) 1 ∧
      ((false : Bool) ∈ holdable.recovery Set.univ ({true} : Set Bool) 1 ↔
        ∃ σ : Bool → List Bool → Bool, ∀ β : ℕ → Bool, ∃ k ≤ 1,
          (holdable.playH σ false β k).1 ∈ ({true} : Set Bool) ∧
            ∀ j < k, (holdable.playH σ false β j).1 ∈ (Set.univ : Set Bool)) :=
  ⟨holdable.recovery_mono_viability (Set.subset_univ _) 1,
    holdable.mem_recovery_iff Set.univ ({true} : Set Bool) 1 false⟩

/-- **A bounded growth rate cannot cross a threshold before its budget runs
out.** A distance that never grows by more than `v` per step, starting far
enough below the critical value, stays below it for the whole window. -/
public theorem safety_not_crossed_of_rate (t : ℕ) (ht : t ≤ 2) :
    (fun _ : ℕ => (0 : ℝ)) t < 1 :=
  not_crossed_of_rate (fun _ => 0) 0 1 le_rfl (fun _ => by norm_num) 2 (by norm_num) t ht


end AISafetyAtlas.Examples.Sovereignty.SafetyGame
