import AISafetyAtlas.LinearSystems.Flow

/-!
Klamka (1972), Introduction, p. 725. The linear time-invariant system has
state equation `ẋ(t) = Ax(t) + Bu(t)` and output equation `y(t) = Cx(t)`
with constant matrices of sizes n × n, n × p, and q × n. The on-row
declarations are `IsTrajectoryOn`, `IsTrajectory`, `outputSignal`, and
`IsSolution` for the integral interpretation of the state equation.

The adjudicated reading leaves the coefficient field and time domain open.
On the real-time, complex-coefficient presentations here, the map is the
identity on the matrices, signals, and chosen form of the state equation.

Checked: `lake env lean docs/provenance/transfers/299-klamka-system.lean`
-/

namespace Transfer299

open AISafetyAtlas.LinearSystems Matrix MeasureTheory

inductive StateForm where
  | classicalOn (times : Set ℝ)
  | classical
  | integral

structure System (n p q : ℕ) where
  A : Matrix (Fin n) (Fin n) ℂ
  B : Matrix (Fin n) (Fin p) ℂ
  C : Matrix (Fin q) (Fin n) ℂ
  x : ℝ → (Fin n → ℂ)
  u : ℝ → (Fin p → ℂ)
  y : ℝ → (Fin q → ℂ)
  form : StateForm

variable {n p q : ℕ}

private def stateEquation (S : System n p q) (form : StateForm) : Prop :=
  match form with
  | .classicalOn times => ∀ t ∈ times, HasDerivAt S.x (S.A *ᵥ S.x t + S.B *ᵥ S.u t) t
  | .classical => ∀ t, HasDerivAt S.x (S.A *ᵥ S.x t + S.B *ᵥ S.u t) t
  | .integral =>
      Continuous S.x ∧
        (∀ a b : ℝ, IntervalIntegrable (fun s ↦ S.A *ᵥ S.x s + S.B *ᵥ S.u s) volume a b) ∧
        ∀ t, S.x t = S.x 0 + ∫ s in (0 : ℝ)..t, (S.A *ᵥ S.x s + S.B *ᵥ S.u s)

def PrintStatement (S : System n p q) : Prop :=
  stateEquation S S.form ∧ ∀ t, S.y t = S.C *ᵥ S.x t

private def leanStateEquation (S : System n p q) (form : StateForm) : Prop :=
  match form with
  | .classicalOn times => IsTrajectoryOn S.A S.B times S.x S.u
  | .classical => IsTrajectory S.A S.B S.x S.u
  | .integral => IsSolution S.A S.B S.x S.u

def LeanStatement (S : System n p q) : Prop :=
  leanStateEquation S S.form ∧ S.y = outputSignal S.C S.x

def phi (S : System n p q) : System n p q := S

private theorem state_equation_iff (S : System n p q) (form : StateForm) :
    leanStateEquation S form ↔ stateEquation S form := by
  cases form with
  | classicalOn times => rfl
  | classical =>
      change (∀ t ∈ (Set.univ : Set ℝ), HasDerivAt S.x (S.A *ᵥ S.x t + S.B *ᵥ S.u t) t) ↔
        ∀ t, HasDerivAt S.x (S.A *ᵥ S.x t + S.B *ᵥ S.u t) t
      simp
  | integral => rfl

theorem defining_condition (S : System n p q) : LeanStatement S ↔ PrintStatement (phi S) := by
  unfold LeanStatement PrintStatement phi
  rw [state_equation_iff]
  exact and_congr_right fun _ ↦ ⟨fun h t ↦ congrFun h t, funext⟩

theorem lean_of_print (S : System n p q) : PrintStatement (phi S) → LeanStatement S :=
  (defining_condition S).mpr

theorem print_of_lean (S : System n p q) : LeanStatement S → PrintStatement S :=
  (defining_condition S).mp

end Transfer299
