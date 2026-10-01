module

public import AISafetyAtlas.Sovereignty.Outnumbered

/-!
# The guard holds because they come one at a time

Two witnesses, one per layer.

`unanimous` is the game form. Everyone must defect for the revolt to succeed,
so the full coalition forces it and a coalition one member short forces
nothing: the absentee is a veto. Coordination costs nothing here, which is the
point -- at a simultaneous move the many win, and the model says so.

`revolt` is the safety game. The state counts how many are currently in revolt,
the guard may put down one per round, and the adversary may add up to `r` per
round. At `r = 1` the guard holds the threshold forever from a quiet start; at
`r = 2` it cannot hold it for a single round. The two adversaries differ in
nothing but the schedule, and `adversaryLe_revolt` says the weaker one's moves
are among the stronger one's, so
`AISafetyAtlas.Sovereignty.safetyKernel_subset_of_adversaryLe` applies and
`kernel_ssubset` says the inclusion it gives is strict.

Nothing here is about incentives. Whether any single prisoner would move first
is a question about preferences, and no preference appears below.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Outnumbered

open AISafetyAtlas.Sovereignty

/-! ## The game form: the win needs everyone -/

/-- **A revolt that succeeds only if nobody abstains.** The outcome is the
proposition that everybody defected, so no decidability is needed anywhere. -/
@[expose] public def unanimous (n : ℕ) : GameForm.{0, 0, 0} (Fin n) Prop where
  strategy _ := Bool
  outcome s := ∀ i, s i = true

/-- Everyone has a move. -/
public instance unanimous_nonempty (n : ℕ) (i : Fin n) :
    Nonempty ((unanimous n).strategy i) := ⟨true⟩

/-- The successful outcomes: the propositions that hold. -/
@[expose] public def succeeds : Set Prop := {P | P}

/-- **The whole body forces the revolt.** Coordination is free at a game form,
which is the honest content: at a simultaneous move the many win. -/
public theorem unanimous_forces_univ (n : ℕ) :
    Forces (unanimous n) Set.univ succeeds := by
  refine ⟨fun _ => true, fun s hs => ?_⟩
  exact fun i => hs ⟨i, Set.mem_univ i⟩

/-- **And any single absentee vetoes it.** -/
public theorem unanimous_veto {n : ℕ} (j : Fin n) :
    Veto (unanimous n) {j} succeeds := by
  refine ⟨fun _ => false, fun s hs => ?_⟩
  have hj : s j = false := hs ⟨j, rfl⟩
  intro hall
  exact absurd (hall j) (by rw [hj]; exact Bool.false_ne_true)

/-- **So a coalition one member short forces nothing**, however large it is. -/
public theorem unanimous_not_forces_of_missing {n : ℕ} {C : Set (Fin n)} {j : Fin n}
    (hj : j ∉ C) : ¬ Forces (unanimous n) C succeeds :=
  not_forces_of_veto_outside (Set.disjoint_singleton_right.mpr hj) (unanimous_veto j)

/-! ## The safety game: the schedule is the whole difference -/

/-- **The prison.** The state is how many are in revolt. The guard either puts
one down or stands by, and up to `r` more join in the same round. -/
@[expose] public def revolt (r : ℕ) : SafetyGame ℕ Bool (Fin (r + 1)) where
  step s a b := (if a then s - 1 else s) + b.val

/-- Being in control: fewer than two in revolt at once. -/
@[expose] public def held : Set ℕ := {s | s ≤ 1}

/-- **Arriving singly is among the ways of arriving in pairs.** -/
public theorem adversaryLe_revolt : AdversaryLe (revolt 1) (revolt 2) :=
  fun _ _ b₁ => ⟨Fin.castLE (by omega) b₁, rfl⟩

/-- **The guard holds against defectors arriving one at a time**, from a quiet
start and forever, with no bound on the horizon. -/
public theorem zero_mem_kernel_single : (0 : ℕ) ∈ (revolt 1).safetyKernel held :=
  (revolt 1).subset_safetyKernel (V := held) (W := held) le_rfl
    (fun s hs => ⟨true, fun b => by
      have hb : b.val ≤ 1 := by omega
      have hs' : s ≤ 1 := hs
      show (if true then s - 1 else s) + b.val ≤ 1
      simp only [if_true]
      omega⟩)
    (by norm_num [held])

/-- **And loses to defectors arriving two at a time**, in one round, from the
same quiet start. No action helps, so this is not a failure of the guard's
strategy. -/
public theorem zero_not_mem_kernel_double : (0 : ℕ) ∉ (revolt 2).safetyKernel held := by
  intro h
  obtain ⟨a, ha⟩ := (revolt 2).safetyKernel_subset_cpre held h
  have hmem := (revolt 2).safetyKernel_subset held (ha ⟨2, by omega⟩)
  have : (if a then (0 : ℕ) - 1 else 0) + 2 ≤ 1 := hmem
  cases a <;> simp at this

/--
**So the kernel inclusion is strict, and the strictness is the guard's power.**

The two adversaries have the same members with the same reach. They differ only
in how many may move in one round, and that difference is the whole of the
guard's position.
-/
public theorem kernel_ssubset :
    (revolt 2).safetyKernel held ⊂ (revolt 1).safetyKernel held :=
  ⟨safetyKernel_subset_of_adversaryLe adversaryLe_revolt held,
    fun hsub => zero_not_mem_kernel_double (hsub zero_mem_kernel_single)⟩

end AISafetyAtlas.Examples.Sovereignty.Outnumbered
