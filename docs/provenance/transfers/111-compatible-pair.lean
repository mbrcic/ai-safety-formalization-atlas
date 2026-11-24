import AISafetyAtlas.Preference.SourceComplexity

/-!
Armstrong & Mindermann (2018), §3.2, p. 3. A pair `(p, R)` is compatible with
`π̇` if `p(R) = π̇`. Print's planner is a map `p : ℛ → Π` from the reward
functions `S × A → [-1, 1]` to the deterministic Markovian policies `S → A`, in
an MDP/R `⟨S, A, T, ŝ⟩` with a finite action space, a transition function and a
start state (§3). The cited declarations are `AISafetyAtlas.Preference.Explains`
(any reward type `R`, any behaviour type `B`) and
`AISafetyAtlas.Preference.Source.ReasonableForF.Compatible` (unbounded real
reward tables, any state type). `compatible_iff` identifies the second with
`ReasonableLanguage.Compatible` and is not needed here.

The map sends a Lean instance `(p, r, b)` to an MDP/R with states `R ⊕ B`,
actions `Bool`, the deterministic self-loop and start state `inl r`. A reward
`r'` is coded by the reward table that pays `1` at `inl r'` and `0` elsewhere,
a behaviour `b'` by the policy that chooses `true` exactly at `inr b'`; both
codes are injective. The image planner decodes a coded reward, applies `p` and
encodes the result (any other reward goes to the constant `false` policy). The
printed equality at the image, `p'(code r) = code b`, holds exactly when
`p r = b`. `Compatible x π` unfolds to `Explains x.1 x.2 π`, so the same map
serves it.

Checked: `lake env lean docs/provenance/transfers/111-compatible-pair.lean`
-/

namespace Transfer111

open AISafetyAtlas.Preference

/-- Print's MDP/R `⟨S, A, T, ŝ⟩` with a finite action space and the transition
function `T : S × A × S → [0, 1]` as printed. Normalization of `T` is not
encoded: compatibility does not read `T`, and the image's `T` is the
deterministic self-loop, normalized on any reading. -/
structure PrintMDP (S A : Type*) [Fintype A] where
  T : S × A × S → ℝ
  T_mem : ∀ x, T x ∈ Set.Icc (0 : ℝ) 1
  start : S

/-- Print's reward space `ℛ = [-1, 1]^{S × A}`. -/
def PrintReward (S A : Type*) : Type _ :=
  {R : S × A → ℝ // ∀ sa, R sa ∈ Set.Icc (-1 : ℝ) 1}

/-- Print's compatibility of `(p, R)` with `π̇` in the MDP/R `M`. -/
def PrintStatement {S A : Type*} [Fintype A] (_M : PrintMDP S A)
    (p : PrintReward S A → (S → A)) (R : PrintReward S A) (π : S → A) : Prop :=
  p R = π

def LeanStatementExplains {R B : Type*} (p : Planner R B) (r : R) (b : B) : Prop :=
  Explains p r b

def LeanStatementCompatible {S A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (x : Pair S A) (π : Policy S A) : Prop :=
  Source.ReasonableForF.Compatible x π

open Classical in
/-- The image MDP/R: states `R ⊕ B`, actions `Bool`, the deterministic self-loop. -/
noncomputable def phiM (R B : Type*) (r : R) : PrintMDP (R ⊕ B) Bool :=
  ⟨fun x => if x.2.2 = x.1 then 1 else 0, fun x => by split_ifs <;> norm_num, Sum.inl r⟩

open Classical in
/-- The reward code of `r'`: reward `1` at the state `inl r'`, `0` elsewhere. -/
noncomputable def codeR {R : Type*} (B : Type*) (r' : R) : PrintReward (R ⊕ B) Bool :=
  ⟨fun sa => if sa.1 = Sum.inl r' then 1 else 0, fun sa => by dsimp only; split_ifs <;> norm_num⟩

open Classical in
/-- The policy code of `b'`: choose `true` exactly at the state `inr b'`. -/
noncomputable def codeB (R : Type*) {B : Type*} (b' : B) : R ⊕ B → Bool :=
  fun s => decide (s = Sum.inr b')

open Classical in
/-- The image planner: decode the reward, apply `p`, encode the behaviour. -/
noncomputable def phiP {R B : Type*} (p : Planner R B) :
    PrintReward (R ⊕ B) Bool → (R ⊕ B → Bool) :=
  fun R' => if h : ∃ r', R' = codeR B r' then codeB R (p h.choose) else fun _ => false

theorem codeR_injective {R : Type*} (B : Type*) {r₁ r₂ : R} (h : codeR B r₁ = codeR B r₂) :
    r₁ = r₂ := by
  classical
  have := congrArg (fun R' : PrintReward (R ⊕ B) Bool => R'.1 (Sum.inl r₁, false)) h
  by_contra hne
  simp [codeR, hne] at this

theorem codeB_injective (R : Type*) {B : Type*} {b₁ b₂ : B} (h : codeB R b₁ = codeB R b₂) :
    b₁ = b₂ := by
  classical
  have := congrFun h (Sum.inr b₁)
  simpa [codeB, eq_comm] using this

theorem phiP_codeR {R B : Type*} (p : Planner R B) (r : R) :
    phiP p (codeR B r) = codeB R (p r) := by
  have h : ∃ r', codeR B r = codeR B r' := ⟨r, rfl⟩
  rw [phiP, dif_pos h, ← codeR_injective B h.choose_spec]

theorem defining_condition_explains {R B : Type*} (p : Planner R B) (r : R) (b : B) :
    LeanStatementExplains p r b ↔
      PrintStatement (phiM R B r) (phiP p) (codeR B r) (codeB R b) := by
  change p r = b ↔ phiP p (codeR B r) = codeB R b
  rw [phiP_codeR]
  exact ⟨fun h => h ▸ rfl, codeB_injective R⟩

theorem defining_condition_compatible {S A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (x : Pair S A) (π : Policy S A) :
    LeanStatementCompatible x π ↔
      PrintStatement (phiM _ _ x.2) (phiP x.1) (codeR _ x.2) (codeB _ π) :=
  defining_condition_explains x.1 x.2 π

theorem lean_of_print_explains {R B : Type*} (p : Planner R B) (r : R) (b : B) :
    PrintStatement (phiM R B r) (phiP p) (codeR B r) (codeB R b) →
      LeanStatementExplains p r b :=
  (defining_condition_explains p r b).mpr

theorem lean_of_print_compatible {S A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (x : Pair S A) (π : Policy S A) :
    PrintStatement (phiM _ _ x.2) (phiP x.1) (codeR _ x.2) (codeB _ π) →
      LeanStatementCompatible x π :=
  (defining_condition_compatible x π).mpr

/-- Every printed instance is an `Explains` instance, at print's own reward type. -/
theorem print_of_lean_explains {S A : Type*} [Fintype A] (M : PrintMDP S A)
    (p : PrintReward S A → (S → A)) (R : PrintReward S A) (π : S → A) :
    LeanStatementExplains p R π ↔ PrintStatement M p R π :=
  Iff.rfl

open Classical in
/-- A printed planner, extended to unbounded reward tables by its value at `R`. -/
noncomputable def extend {S A : Type*} (p : PrintReward S A → (S → A)) (R : PrintReward S A) :
    Planner (RewardFn S A) (Policy S A) :=
  fun r => if h : ∀ sa : S × A, r sa.1 sa.2 ∈ Set.Icc (-1 : ℝ) 1 then
    p ⟨fun sa => r sa.1 sa.2, h⟩ else p R

/-- Every printed instance with a nonempty action set is a `Compatible` instance.
An empty action set has no policy on a nonempty state set, so no printed instance. -/
theorem print_of_lean_compatible {S A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (M : PrintMDP S A) (p : PrintReward S A → (S → A)) (R : PrintReward S A) (π : S → A) :
    LeanStatementCompatible (extend p R, fun s a => R.1 (s, a)) π ↔ PrintStatement M p R π := by
  change extend p R (fun s a => R.1 (s, a)) = π ↔ p R = π
  rw [extend, dif_pos fun sa => R.2 sa]
  exact Iff.rfl

end Transfer111
