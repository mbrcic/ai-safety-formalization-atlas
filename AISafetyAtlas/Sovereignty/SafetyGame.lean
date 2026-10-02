module

public import AISafetyAtlas.Sovereignty.Influence
public import Mathlib.Order.FixedPoints

/-!
# Keeping a system inside a set, forever and after a shock

The proposal's §6 is its dynamic core. A controller picks an action, an
adversary answers it, and the state moves. Two questions follow: from where can
the controller keep the state inside a protected set forever, and from where
can it get back into a good region within a budget without leaving the
protected set on the way.

## The controllable predecessor, and the kernel as a fixed point

`cpre W` is the set of states from which one action keeps every answer inside
`W`. Print builds the kernel by iterating `V ∩ cpre ·` downward from `V` and
argues it stabilizes after at most `|S|` strict removal rounds.

`safetyKernel` is the same object taken as a **greatest fixed point** instead.
That is deliberate and it is a scope change in both directions:

* **wider** — no finiteness anywhere, so the characterization holds on infinite
  state spaces where print's counting argument says nothing;
* **narrower** — the `|S|`-round *rate* is print's and is not proved here. The
  object is the same; the bound on how long it takes to compute is not.

`mem_safetyKernel_iff_exists_maintaining` is `D1`'s substance: a state is in
the kernel exactly when some positional controller keeps every play inside the
protected set for all time. The forward direction chooses one witnessing action
per state and inducts; the reverse takes the states actually visited under the
controller as the invariant set. Neither needs the game to be finite, and
neither needs the play to be finite.

## Recovery

`recovery` iterates upward and `recovery_reaches` is the
direction of `D2` that an engineer uses: membership within budget `H` yields a
controller reaching the target within `H` steps while holding the protected set
until it arrives. `mem_recovery_of_recovers` is the converse, and it is stated
against controllers that remember the whole history of answers, so the recovery
sets are not merely where a memoryless controller succeeds. `mem_recovery_iff`
puts the two together as print's equivalence. `recovery_mono` and
`recovery_mono_viability` are `D3`.

## Latency

`danger_le_of_rate` is `D5`, which is arithmetic and has no game in it: a
quantity starting at `d₀` and growing by at most `v` per step is at most
`d₀ + v * L` at every time up to `L`. Print's conditional form -- that the
threshold cannot be crossed before the intervention lands -- is the corollary
`not_crossed_of_rate`, and print's own caveat applies unchanged: a continued
guarantee needs the post-intervention dynamics to be safe, and nothing here
says anything about those.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

/--
**A safety game.** The controller picks an action, the adversary answers, and
the state moves. Deterministic and fully observed, as print's §6.1 is.
-/
public structure SafetyGame (S : Type u) (A : Type v) (B : Type w) where
  /-- Where the state goes under an action and an answer. -/
  step : S → A → B → S

namespace SafetyGame

variable {S : Type u} {A : Type v} {B : Type w} (Γ : SafetyGame S A B)

/-- **The controllable predecessor.** One action keeps every answer inside `W`. -/
@[expose] public def cpre (W : Set S) : Set S :=
  {s | ∃ a : A, ∀ b : B, Γ.step s a b ∈ W}

/-- It is monotone, which is what makes every fixed point below exist. -/
public theorem cpre_mono {W W' : Set S} (h : W ⊆ W') : Γ.cpre W ⊆ Γ.cpre W' := by
  rintro s ⟨a, ha⟩
  exact ⟨a, fun b => h (ha b)⟩

/-- The one-step operator whose greatest fixed point is the kernel. -/
@[expose] public def keep (V : Set S) : Set S →o Set S where
  toFun W := V ∩ Γ.cpre W
  monotone' _ _ h := Set.inter_subset_inter_right _ (Γ.cpre_mono h)

/--
**The controlled-invariant kernel.** The largest set inside `V` from which the
controller can always stay inside itself.
-/
@[expose] public def safetyKernel (V : Set S) : Set S :=
  OrderHom.gfp (Γ.keep V)

/-- The kernel sits inside the protected set. -/
public theorem safetyKernel_subset (V : Set S) : Γ.safetyKernel V ⊆ V := by
  conv_lhs => rw [safetyKernel, ← OrderHom.map_gfp (Γ.keep V)]
  exact Set.inter_subset_left

/-- **Anything that keeps itself inside `V` is inside the kernel.** This is the
Knaster--Tarski half, and it is the form in which a certificate is checked: a
set, an action per state, and closure. -/
public theorem subset_safetyKernel {V W : Set S} (hV : W ⊆ V)
    (hclosed : W ⊆ Γ.cpre W) : W ⊆ Γ.safetyKernel V :=
  OrderHom.le_gfp _ (Set.subset_inter hV hclosed)

/-- And the kernel keeps itself. -/
public theorem safetyKernel_subset_cpre (V : Set S) :
    Γ.safetyKernel V ⊆ Γ.cpre (Γ.safetyKernel V) := by
  conv_lhs => rw [safetyKernel, ← OrderHom.map_gfp (Γ.keep V)]
  exact Set.inter_subset_right

/-! ## Plays, and what a controller maintains -/

/-- The state at time `n` when the controller plays positionally and the
adversary plays the answer sequence `β`. -/
@[expose] public def play (σ : S → A) (s₀ : S) (β : ℕ → B) : ℕ → S
  | 0 => s₀
  | n + 1 => Γ.step (play σ s₀ β n) (σ (play σ s₀ β n)) (β n)

@[simp] public theorem play_zero (σ : S → A) (s₀ : S) (β : ℕ → B) :
    Γ.play σ s₀ β 0 = s₀ := rfl

@[simp] public theorem play_succ (σ : S → A) (s₀ : S) (β : ℕ → B) (n : ℕ) :
    Γ.play σ s₀ β (n + 1)
      = Γ.step (Γ.play σ s₀ β n) (σ (Γ.play σ s₀ β n)) (β n) := rfl

/-- **A controller maintains `V` from `s₀`** when every play stays inside it. -/
@[expose] public def Maintains (σ : S → A) (V : Set S) (s₀ : S) : Prop :=
  ∀ β : ℕ → B, ∀ n : ℕ, Γ.play σ s₀ β n ∈ V

/--
**`D1`: the kernel is exactly where the protected set can be held forever.**

Print states this for a finite game and adds that the downward iteration
stabilizes after at most `|S|` strict removal rounds. The rate is print's and
is not proved here; the characterization is, and without any finiteness.
-/
public theorem mem_safetyKernel_iff_exists_maintaining [Nonempty A] [Nonempty B]
    (V : Set S) (s₀ : S) :
    s₀ ∈ Γ.safetyKernel V ↔ ∃ σ : S → A, Γ.Maintains σ V s₀ := by
  classical
  constructor
  · intro hs
    set W := Γ.safetyKernel V with hW
    have hclosed : W ⊆ Γ.cpre W := Γ.safetyKernel_subset_cpre V
    refine ⟨fun s => if h : s ∈ W then (hclosed h).choose else Classical.arbitrary A,
      fun β n => ?_⟩
    have hstay : ∀ m, Γ.play (fun s => if h : s ∈ W then (hclosed h).choose
        else Classical.arbitrary A) s₀ β m ∈ W := by
      intro m
      induction m with
      | zero => exact hs
      | succ k ih =>
          have := (hclosed ih).choose_spec (β k)
          simpa [play_succ, dif_pos ih] using this
    exact Γ.safetyKernel_subset V (hstay n)
  · rintro ⟨σ, hσ⟩
    have hmem : s₀ ∈ {s | ∃ β n, Γ.play σ s₀ β n = s} :=
      ⟨fun _ => Classical.arbitrary B, 0, rfl⟩
    refine Γ.subset_safetyKernel (W := {s | ∃ β n, Γ.play σ s₀ β n = s}) ?_ ?_ hmem
    · rintro _ ⟨β, n, rfl⟩
      exact hσ β n
    · rintro _ ⟨β, n, rfl⟩
      refine ⟨σ (Γ.play σ s₀ β n), fun b => ?_⟩
      refine ⟨fun k => if k = n then b else β k, n + 1, ?_⟩
      have hpre : ∀ m, m ≤ n → Γ.play σ s₀ (fun k => if k = n then b else β k) m
          = Γ.play σ s₀ β m := by
        intro m
        induction m with
        | zero => intro _; rfl
        | succ k ih =>
            intro hm
            have hk : k < n := hm
            simp only [play_succ, ih (Nat.le_of_lt hk), if_neg (Nat.ne_of_lt hk)]
      simp only [play_succ, hpre n le_rfl, if_pos]

/-! ## Recovery within a budget -/

/-- **The recovery sets.** `recovery V W H` is where the controller can reach
`W` within `H` steps without leaving `V` on the way. -/
@[expose] public def recovery (V W : Set S) : ℕ → Set S
  | 0 => W
  | n + 1 => recovery V W n ∪ (V ∩ Γ.cpre (recovery V W n))

/-- **`D3`: a larger budget cannot recover less.** -/
public theorem recovery_mono (V W : Set S) (n : ℕ) :
    Γ.recovery V W n ⊆ Γ.recovery V W (n + 1) :=
  fun _ hs => Or.inl hs

/-- And the recovery sets are monotone in the budget throughout. -/
public theorem recovery_mono_budget (V W : Set S) {m n : ℕ} (h : m ≤ n) :
    Γ.recovery V W m ⊆ Γ.recovery V W n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hm | hm
      · exact (ih (Nat.lt_succ_iff.mp hm)).trans (Γ.recovery_mono V W k)
      · rw [Nat.le_antisymm h hm]

/-! ### `D2`: the budget is a rank, and the rank is a controller

A positional controller suffices, and the reason is that the recovery sets are
built by one upward iteration: a state first admitted at stage `k + 1` is in
the viability set and has an action sending every answer into stage `k`. The
least stage at which a state is admitted is therefore a rank that the
controller can always decrease.
-/

open Classical in
/-- **The least budget at which a state is already recoverable.** -/
@[expose] public noncomputable def recoveryRank (V W : Set S) (s : S) : ℕ :=
  if h : ∃ n, s ∈ Γ.recovery V W n then Nat.find h else 0

/-- A recoverable state is recovered at its own rank. -/
public theorem mem_recovery_recoveryRank {V W : Set S} {s : S}
    (h : ∃ n, s ∈ Γ.recovery V W n) :
    s ∈ Γ.recovery V W (Γ.recoveryRank V W s) := by
  classical
  rw [recoveryRank, dif_pos h]
  exact Nat.find_spec h

/-- And at no smaller one. -/
public theorem recoveryRank_le {V W : Set S} {s : S} {n : ℕ}
    (hs : s ∈ Γ.recovery V W n) : Γ.recoveryRank V W s ≤ n := by
  classical
  have h : ∃ m, s ∈ Γ.recovery V W m := ⟨n, hs⟩
  rw [recoveryRank, dif_pos h]
  exact Nat.find_le hs

open Classical in
/-- An action driving every answer into a named stage, where one exists. -/
@[expose] public noncomputable def recoveryAction [Nonempty A] (V W : Set S)
    (k : ℕ) (s : S) : A :=
  if h : ∃ a : A, ∀ b : B, Γ.step s a b ∈ Γ.recovery V W k then h.choose
  else Classical.arbitrary A

/-- It does what it was chosen for. -/
public theorem recoveryAction_spec [Nonempty A] {V W : Set S} {k : ℕ} {s : S}
    (h : ∃ a : A, ∀ b : B, Γ.step s a b ∈ Γ.recovery V W k) (b : B) :
    Γ.step s (Γ.recoveryAction V W k s) b ∈ Γ.recovery V W k := by
  classical
  rw [recoveryAction, dif_pos h]
  exact h.choose_spec b

/-- **The rank-decreasing controller.** At a state first admitted at stage
`k + 1` it plays an action sending every answer into stage `k`. -/
@[expose] public noncomputable def recoveryStrategy [Nonempty A] (V W : Set S)
    (s : S) : A :=
  Γ.recoveryAction V W (Γ.recoveryRank V W s - 1) s

/-- **A state with positive rank is viable and its successors have smaller
rank.** -/
public theorem recoveryStrategy_step [Nonempty A] {V W : Set S} {s : S} {k : ℕ}
    (hex : ∃ n, s ∈ Γ.recovery V W n) (hrank : Γ.recoveryRank V W s = k + 1) :
    s ∈ V ∧ ∀ b : B, Γ.step s (Γ.recoveryStrategy V W s) b ∈ Γ.recovery V W k := by
  classical
  have hmem : s ∈ Γ.recovery V W (k + 1) := hrank ▸ Γ.mem_recovery_recoveryRank hex
  have hnot : s ∉ Γ.recovery V W k := fun hk => by
    have := Γ.recoveryRank_le hk
    omega
  have hsplit : s ∈ V ∩ Γ.cpre (Γ.recovery V W k) := by
    rcases hmem with h | h
    · exact absurd h hnot
    · exact h
  have hkk : Γ.recoveryRank V W s - 1 = k := by omega
  refine ⟨hsplit.1, fun b => ?_⟩
  show Γ.step s (Γ.recoveryAction V W (Γ.recoveryRank V W s - 1) s) b ∈ _
  rw [hkk]
  exact Γ.recoveryAction_spec hsplit.2 b

/-- Playing one step and shifting the adversary. -/
public theorem play_shift (σ : S → A) (s₀ : S) (β : ℕ → B) (n : ℕ) :
    Γ.play σ s₀ β (n + 1)
      = Γ.play σ (Γ.step s₀ (σ s₀) (β 0)) (fun j => β (j + 1)) n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [play_succ, ih, play_succ]

/--
**`D2`: membership within a budget is a controller that recovers within it.**

From a state of rank at most `H` the rank-decreasing controller reaches the
target within `H` steps against every adversary, and stays inside the
viability set until it arrives.

Print states the equivalence; this is the direction a controller is built
from, and the witness is positional. The converse is
`mem_recovery_of_recovers`, and `mem_recovery_iff` is the equivalence.
-/
public theorem recovery_reaches [Nonempty A] (V W : Set S) :
    ∀ (H : ℕ) (s₀ : S), (∃ n, s₀ ∈ Γ.recovery V W n) →
      Γ.recoveryRank V W s₀ ≤ H → ∀ β : ℕ → B,
        ∃ k ≤ H, Γ.play (Γ.recoveryStrategy V W) s₀ β k ∈ W ∧
          ∀ j < k, Γ.play (Γ.recoveryStrategy V W) s₀ β j ∈ V := by
  classical
  intro H
  induction H with
  | zero =>
      intro s₀ hex hrank β
      have h0 : Γ.recoveryRank V W s₀ = 0 := Nat.le_zero.mp hrank
      have : s₀ ∈ Γ.recovery V W 0 := h0 ▸ Γ.mem_recovery_recoveryRank hex
      exact ⟨0, le_rfl, this, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ H ih =>
      intro s₀ hex hrank β
      rcases Nat.eq_zero_or_pos (Γ.recoveryRank V W s₀) with h0 | hpos
      · have : s₀ ∈ Γ.recovery V W 0 := h0 ▸ Γ.mem_recovery_recoveryRank hex
        exact ⟨0, Nat.zero_le _, this, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      · obtain ⟨k, hk⟩ : ∃ k, Γ.recoveryRank V W s₀ = k + 1 :=
          ⟨Γ.recoveryRank V W s₀ - 1, by omega⟩
        obtain ⟨hV, hstep⟩ := Γ.recoveryStrategy_step hex hk
        have hex₁ : ∃ n,
            Γ.step s₀ (Γ.recoveryStrategy V W s₀) (β 0) ∈ Γ.recovery V W n :=
          ⟨k, hstep (β 0)⟩
        have hrank₁ : Γ.recoveryRank V W
            (Γ.step s₀ (Γ.recoveryStrategy V W s₀) (β 0)) ≤ H := by
          have h2 := Γ.recoveryRank_le (hstep (β 0))
          omega
        obtain ⟨m, hmH, hmW, hmV⟩ := ih _ hex₁ hrank₁ (fun j => β (j + 1))
        refine ⟨m + 1, by omega, ?_, ?_⟩
        · rw [Γ.play_shift]; exact hmW
        · intro j hj
          rcases Nat.eq_zero_or_pos j with rfl | hjpos
          · simpa using hV
          · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
            rw [Γ.play_shift]
            exact hmV i (by omega)


/-! ## The converse of `D2`, against controllers that remember everything -/

/-- **Prefixing one answer to an adversary's sequence.** -/
@[expose] public def consStream (b : B) (β : ℕ → B) : ℕ → B
  | 0 => b
  | n + 1 => β n

@[simp] public theorem consStream_zero (b : B) (β : ℕ → B) :
    consStream b β 0 = b := rfl

@[simp] public theorem consStream_succ (b : B) (β : ℕ → B) (n : ℕ) :
    consStream b β (n + 1) = β n := rfl

/--
**A controller that sees the whole history.** It reads the current state and
the list of answers so far, most recent first, and returns an action together
with the extended history. A positional controller is the special case that
ignores the second argument, which is `playH_positional`.

The converse direction of `D2` is stated at this strategy type and not at the
positional one, so that it rules out *every* controller and not only the
memoryless ones. The forward direction stays positional, which is the stronger
reading there.
-/
@[expose] public def playH (σ : S → List B → A) (s₀ : S) (β : ℕ → B) :
    ℕ → S × List B
  | 0 => (s₀, [])
  | n + 1 =>
      (Γ.step (playH σ s₀ β n).1 (σ (playH σ s₀ β n).1 (playH σ s₀ β n).2) (β n),
        β n :: (playH σ s₀ β n).2)

@[simp] public theorem playH_zero (σ : S → List B → A) (s₀ : S) (β : ℕ → B) :
    Γ.playH σ s₀ β 0 = (s₀, []) := rfl

@[simp] public theorem playH_succ (σ : S → List B → A) (s₀ : S) (β : ℕ → B)
    (n : ℕ) :
    Γ.playH σ s₀ β (n + 1) =
      (Γ.step (Γ.playH σ s₀ β n).1 (σ (Γ.playH σ s₀ β n).1 (Γ.playH σ s₀ β n).2)
          (β n),
        β n :: (Γ.playH σ s₀ β n).2) := rfl

/-- **A positional controller is a forgetful history-dependent one.** -/
public theorem playH_positional (σ : S → A) (s₀ : S) (β : ℕ → B) (n : ℕ) :
    (Γ.playH (fun s _ => σ s) s₀ β n).1 = Γ.play σ s₀ β n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [playH_succ, play_succ, ih]

/-- **Playing one step and shifting the adversary**, for a controller with
memory: the continuation is the same controller with the first answer already
appended to every history it will see. -/
public theorem playH_shift (σ : S → List B → A) (s₀ : S) (b : B) (β : ℕ → B)
    (n : ℕ) :
    Γ.playH σ s₀ (consStream b β) (n + 1) =
      (((Γ.playH (fun s h => σ s (h ++ [b])) (Γ.step s₀ (σ s₀ []) b) β n).1),
        (Γ.playH (fun s h => σ s (h ++ [b])) (Γ.step s₀ (σ s₀ []) b) β n).2
          ++ [b]) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Γ.playH_succ, ih, Γ.playH_succ]; simp

/--
**`D2`, converse: a controller that recovers within `H` puts the state in the
recovery set of budget `H`.**

Together with `recovery_reaches` this is print's equivalence. The quantifier
here is over controllers with unbounded memory, so the recovery sets are not
merely the states from which a *memoryless* controller succeeds: no controller
of any kind succeeds from outside them.
-/
public theorem mem_recovery_of_recovers [Nonempty B] (V W : Set S) :
    ∀ (H : ℕ) (σ : S → List B → A) (s₀ : S),
      (∀ β : ℕ → B, ∃ k ≤ H, (Γ.playH σ s₀ β k).1 ∈ W ∧
        ∀ j < k, (Γ.playH σ s₀ β j).1 ∈ V) →
      s₀ ∈ Γ.recovery V W H := by
  classical
  intro H
  induction H with
  | zero =>
      intro σ s₀ h
      obtain ⟨k, hk, hW, -⟩ := h fun _ => Classical.arbitrary B
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      exact hW
  | succ H ih =>
      intro σ s₀ h
      by_cases hs : s₀ ∈ W
      · exact Γ.recovery_mono_budget V W (Nat.zero_le _) hs
      · have hV : s₀ ∈ V := by
          obtain ⟨k, -, hW, hVj⟩ := h fun _ => Classical.arbitrary B
          have hk0 : 0 < k := by
            rcases Nat.eq_zero_or_pos k with rfl | hp
            · exact absurd (by simpa using hW) hs
            · exact hp
          simpa using hVj 0 hk0
        refine Set.mem_union_right _ ⟨hV, ⟨σ s₀ [], fun b => ?_⟩⟩
        refine ih (fun s hist => σ s (hist ++ [b])) _ fun β => ?_
        obtain ⟨k, hk, hW, hVj⟩ := h (consStream b β)
        have hk0 : 0 < k := by
          rcases Nat.eq_zero_or_pos k with rfl | hp
          · exact absurd (by simpa using hW) hs
          · exact hp
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        refine ⟨m, by omega, ?_, fun j hj => ?_⟩
        · rw [Γ.playH_shift] at hW; exact hW
        · have := hVj (j + 1) (by omega)
          rw [Γ.playH_shift] at this; exact this

/--
**`D2` as print states it**: membership in the recovery set of budget `H` is
exactly the existence of a controller that reaches the target within `H` steps
while holding the viability set until it arrives.

The witness produced by the forward direction is positional, and the converse
refutes controllers with memory, so neither direction is weakened by the
strategy type.
-/
public theorem mem_recovery_iff [Nonempty A] [Nonempty B] (V W : Set S) (H : ℕ)
    (s₀ : S) :
    s₀ ∈ Γ.recovery V W H ↔
      ∃ σ : S → List B → A, ∀ β : ℕ → B, ∃ k ≤ H,
        (Γ.playH σ s₀ β k).1 ∈ W ∧ ∀ j < k, (Γ.playH σ s₀ β j).1 ∈ V := by
  constructor
  · intro hs
    refine ⟨fun s _ => Γ.recoveryStrategy V W s, fun β => ?_⟩
    obtain ⟨k, hk, hW, hVj⟩ :=
      Γ.recovery_reaches V W H s₀ ⟨H, hs⟩ (Γ.recoveryRank_le hs) β
    exact ⟨k, hk, by rw [Γ.playH_positional]; exact hW,
      fun j hj => by rw [Γ.playH_positional]; exact hVj j hj⟩
  · rintro ⟨σ, hσ⟩
    exact Γ.mem_recovery_of_recovers V W H σ s₀ hσ

/-- **`D3`, second half: enlarging the viability set cannot recover less.** -/
public theorem recovery_mono_viability {V V' W : Set S} (h : V ⊆ V') (n : ℕ) :
    Γ.recovery V W n ⊆ Γ.recovery V' W n := by
  induction n with
  | zero => exact le_rfl
  | succ k ih =>
      exact Set.union_subset_union ih
        (Set.inter_subset_inter h (Γ.cpre_mono ih))

/-! ## `D4`: two systems that do not interact -/

/--
**The product game.** Independent action resources and factorized transitions,
which are print's two hypotheses and are here built into the object rather than
assumed about a given game.
-/
@[expose] public def prodGame {S₁ A₁ B₁ S₂ A₂ B₂ : Type*}
    (Γ₁ : SafetyGame S₁ A₁ B₁) (Γ₂ : SafetyGame S₂ A₂ B₂) :
    SafetyGame (S₁ × S₂) (A₁ × A₂) (B₁ × B₂) where
  step s a b := (Γ₁.step s.1 a.1 b.1, Γ₂.step s.2 a.2 b.2)

/-- A play in the product is the pair of plays in the factors. -/
public theorem play_prodGame {S₁ A₁ B₁ S₂ A₂ B₂ : Type*}
    (Γ₁ : SafetyGame S₁ A₁ B₁) (Γ₂ : SafetyGame S₂ A₂ B₂)
    (σ₁ : S₁ → A₁) (σ₂ : S₂ → A₂) (s₁ : S₁) (s₂ : S₂) (β : ℕ → B₁ × B₂) (n : ℕ) :
    (Γ₁.prodGame Γ₂).play (fun s => (σ₁ s.1, σ₂ s.2)) (s₁, s₂) β n
      = (Γ₁.play σ₁ s₁ (fun k => (β k).1) n, Γ₂.play σ₂ s₂ (fun k => (β k).2) n) := by
  induction n with
  | zero => rfl
  | succ k ih => rw [play_succ, ih]; rfl

/--
**`D4`: local invariants compose when nothing is shared.**

Two controllers that each maintain their own protected set maintain the
product. Print's caveat is that without independent executability and
factorized transitions the local proofs establish nothing about the product;
here that caveat is the definition of `prodGame`, so the theorem cannot be
misapplied to a system that shares a resource.
-/
public theorem maintains_prodGame {S₁ A₁ B₁ S₂ A₂ B₂ : Type*}
    (Γ₁ : SafetyGame S₁ A₁ B₁) (Γ₂ : SafetyGame S₂ A₂ B₂)
    {σ₁ : S₁ → A₁} {σ₂ : S₂ → A₂} {V₁ : Set S₁} {V₂ : Set S₂} {s₁ : S₁} {s₂ : S₂}
    (h₁ : Γ₁.Maintains σ₁ V₁ s₁) (h₂ : Γ₂.Maintains σ₂ V₂ s₂) :
    (Γ₁.prodGame Γ₂).Maintains (fun s => (σ₁ s.1, σ₂ s.2)) (V₁ ×ˢ V₂) (s₁, s₂) := by
  intro β n
  rw [Set.mem_prod, play_prodGame]
  exact ⟨h₁ _ n, h₂ _ n⟩

end SafetyGame

/-! ## `D5`: how far a danger can grow before the intervention lands -/

/--
**`D5`: a bounded growth rate bounds the excursion.** A quantity starting at
`d 0` and growing by at most `v` per step is at most `d 0 + v * L` at every
time up to `L`.
-/
public theorem danger_le_of_rate (d : ℕ → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hgrow : ∀ t, d (t + 1) ≤ d t + v) (L : ℕ) :
    ∀ t ≤ L, d t ≤ d 0 + v * L := by
  have hstep : ∀ t, d t ≤ d 0 + v * t := by
    intro t
    induction t with
    | zero => simp
    | succ k ih =>
        have hcast : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
        calc d (k + 1) ≤ d k + v := hgrow k
          _ ≤ (d 0 + v * k) + v := by linarith
          _ = d 0 + v * ((k : ℝ) + 1) := by ring
          _ = d 0 + v * ((k + 1 : ℕ) : ℝ) := by rw [hcast]
  intro t ht
  refine (hstep t).trans ?_
  have : (t : ℝ) ≤ L := by exact_mod_cast ht
  nlinarith

/-- **And the threshold is not crossed before the intervention lands**, which
is print's conditional form. A continued guarantee needs the post-intervention
dynamics to be safe, and nothing here says anything about those. -/
public theorem not_crossed_of_rate (d : ℕ → ℝ) (v crit : ℝ) (hv : 0 ≤ v)
    (hgrow : ∀ t, d (t + 1) ≤ d t + v) (L : ℕ) (hsafe : d 0 + v * L < crit) :
    ∀ t ≤ L, d t < crit :=
  fun t ht => lt_of_le_of_lt (danger_le_of_rate d v hv hgrow L t ht) hsafe


end AISafetyAtlas.Sovereignty
