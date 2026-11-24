import AISafetyAtlas.Preference

/-!
Armstrong & Mindermann (2018), Theorem 1 (first paragraph), p. 4. "For all
`π ∈ Π` and `R ∈ ℛ`, there exists a `p ∈ 𝒫` such that `p(R) = π`." Here `Π` is
the deterministic Markovian policies `S → A` and `ℛ = [-1, 1]^{S × A}` of an
MDP/R `⟨S, A, T, ŝ⟩` with a finite action space (§3), and a planner is a map
`p : ℛ → Π` (§3.1). The cited declarations are
`AISafetyAtlas.Preference.exists_planner` (any reward type `R`, any behaviour
type `B`) and `consistent_rewards_eq_univ` (its set form).

The map sends a Lean instance `(R, B, r, b)` to the MDP/R with states `R ⊕ B`,
actions `Bool`, the deterministic self-loop and start state `inl r`; the reward
`r` is coded by the table paying `1` at `inl r` and `0` elsewhere, the
behaviour `b` by the policy choosing `true` exactly at `inr b` (both codes are
injective, as in transfer 111). From the printed planner `p'` with
`p'(code r) = code b`, the Lean planner codes its reward, applies `p'` and
decodes the policy (any policy that is not a code goes to `b`). Injectivity of
the policy code turns print's equality into `p r = b`. The set form follows
pointwise from the same map.

Checked: `lake env lean docs/provenance/transfers/127-exists-planner.lean`
-/

namespace Transfer127

open AISafetyAtlas.Preference

universe u v

/-- Print's MDP/R `⟨S, A, T, ŝ⟩` with a finite action space; `T` as printed. -/
structure PrintMDP (S : Type u) (A : Type v) [Fintype A] where
  T : S × A × S → ℝ
  T_mem : ∀ x, T x ∈ Set.Icc (0 : ℝ) 1
  start : S

/-- Print's reward space `ℛ = [-1, 1]^{S × A}`. -/
def PrintReward (S : Type u) (A : Type v) : Type (max u v) :=
  {R : S × A → ℝ // ∀ sa, R sa ∈ Set.Icc (-1 : ℝ) 1}

/-- Print's Theorem 1, first paragraph, in every MDP/R. -/
def PrintStatement : Prop :=
  ∀ (S : Type u) (A : Type v) [Fintype A] (_M : PrintMDP S A) (π : S → A) (R : PrintReward S A),
    ∃ p : PrintReward S A → (S → A), p R = π

/-- The two cited statements. -/
def LeanStatement : Prop :=
  (∀ (R B : Type u) (b : B) (r : R), ∃ p : Planner R B, Explains p r b) ∧
    ∀ (R B : Type u) (b : B), {r : R | ∃ p : Planner R B, Explains p r b} = Set.univ

open Classical in
noncomputable def phiM (R B : Type u) (r : R) : PrintMDP (R ⊕ B) Bool :=
  ⟨fun x => if x.2.2 = x.1 then 1 else 0, fun x => by split_ifs <;> norm_num, Sum.inl r⟩

open Classical in
noncomputable def codeR {R : Type u} (B : Type u) (r' : R) : PrintReward (R ⊕ B) Bool :=
  ⟨fun sa => if sa.1 = Sum.inl r' then 1 else 0, fun sa => by dsimp only; split_ifs <;> norm_num⟩

open Classical in
noncomputable def codeB (R : Type u) {B : Type u} (b' : B) : R ⊕ B → Bool :=
  fun s => decide (s = Sum.inr b')

theorem codeB_injective (R : Type u) {B : Type u} {b₁ b₂ : B}
    (h : codeB R b₁ = codeB R b₂) : b₁ = b₂ := by
  classical
  have := congrFun h (Sum.inr b₁)
  simpa [codeB, eq_comm] using this

open Classical in
/-- Decode a policy to a behaviour; non-codes go to the fallback `b`. -/
noncomputable def decodeB {R B : Type u} (b : B) (π : R ⊕ B → Bool) : B :=
  if h : ∃ b', π = codeB R b' then h.choose else b

theorem decodeB_codeB {R B : Type u} (b b' : B) : decodeB (R := R) b (codeB R b') = b' := by
  have h : ∃ b'', codeB R b' = codeB R b'' := ⟨b', rfl⟩
  rw [decodeB, dif_pos h]
  exact (codeB_injective R h.choose_spec).symm

/-- The print instance of a Lean instance `(R, B, r, b)`. -/
noncomputable def phi (R B : Type u) (r : R) (b : B) :
    PrintMDP (R ⊕ B) Bool × (R ⊕ B → Bool) × PrintReward (R ⊕ B) Bool :=
  (phiM R B r, codeB R b, codeR B r)

/-- (H): print's only hypothesis is the instance itself, an MDP/R with a finite
action space; `phi` supplies one. -/
theorem H (R B : Type u) (r : R) : Nonempty (PrintMDP (R ⊕ B) Bool) := ⟨phiM R B r⟩

/-- (C): print's conclusion at `phi` gives the Lean conclusion. -/
theorem C {R B : Type u} (r : R) (b : B)
    (hP : ∃ p' : PrintReward (R ⊕ B) Bool → (R ⊕ B → Bool),
      p' (phi R B r b).2.2 = (phi R B r b).2.1) :
    ∃ p : Planner R B, Explains p r b := by
  obtain ⟨p', hp'⟩ := hP
  refine ⟨fun r' => decodeB b (p' (codeR B r')), ?_⟩
  change decodeB b (p' (codeR B r)) = b
  change p' (codeR B r) = codeB R b at hp'
  rw [hp', decodeB_codeB]

theorem lean_of_print : PrintStatement.{u, 0} → LeanStatement.{u} := by
  intro hP
  have h1 : ∀ (R B : Type u) (b : B) (r : R), ∃ p : Planner R B, Explains p r b :=
    fun R B b r => C r b (hP (R ⊕ B) Bool (phi R B r b).1 (phi R B r b).2.1 (phi R B r b).2.2)
  exact ⟨h1, fun R B b => Set.eq_univ_of_forall fun r => h1 R B b r⟩

theorem print_of_lean : LeanStatement.{max u v} → PrintStatement.{u, v} :=
  fun hL S A _ _ π R => hL.1 (PrintReward S A) (S → A) π R

end Transfer127
