module

public import AISafetyAtlas.Decision.EpisodicValue

/-!
# The episodic value, worked on an infinite state space

The chain `s ↦ s + 1` on `ℕ`, one action. A reward of `1` at every state has
`T`-step value `T` (`vPiEpisodic_const_reward`); the recursion is also run by
hand at horizon `2` for a reward paying only at state `0`, where the value is
not constant.
-/

namespace AISafetyAtlas.Examples.Decision.EpisodicValue

open AISafetyAtlas.Decision

/-- The chain on `ℕ` with one action. -/
@[expose] public noncomputable def chain₁ : MDP ℕ Unit := MDP.ofDet fun s _ => s + 1

/-- A constant reward of `1` gives `T`-step value `T`. -/
public theorem chain₁_const (T : ℕ) :
    vPiEpisodic chain₁ (fun _ _ => 1) T (fun _ => ()) = fun _ => (T : ℝ) := by
  rw [vPiEpisodic_const_reward chain₁ _ _ 1 (fun _ => rfl) T]
  simp

/-- The bound `T · C` at that reward. -/
example (T : ℕ) (s : ℕ) :
    |vPiEpisodic chain₁ (fun _ _ => 1) T (fun _ => ()) s| ≤ T * 1 :=
  abs_vPiEpisodic_le chain₁ _ _ (fun _ => by simp) T s

/-- A reward paying `1` at state `0` only: over two steps from `0` the value is
`1`, and from `1` it is `0`. -/
public theorem chain₁_tip :
    vPiEpisodic chain₁ (fun s _ => if s = 0 then 1 else 0) 2 (fun _ => ()) 0 = 1 ∧
      vPiEpisodic chain₁ (fun s _ => if s = 0 then 1 else 0) 2 (fun _ => ()) 1 = 0 := by
  simp [vPiEpisodic_succ, chain₁, MDP.ofDet]

example (s : ℕ) : vPiEpisodic chain₁ (fun _ _ => 1) 0 (fun _ => ()) s = 0 :=
  AISafetyAtlas.Decision.vPiEpisodic_zero chain₁ _ _ s

end AISafetyAtlas.Examples.Decision.EpisodicValue
