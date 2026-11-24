import AISafetyAtlas.Sovereignty.EUDetermined

/-!
Turner and Tadepalli, *Parametrically Retargetable Decision-Makers Tend To Seek Power*
(2022), Lemma B.10, p. 20. If the listed permutations fix `C` and the score
`h(A, C, θ)` increases under joint permutation, so does the section `h(·, C, ·)`
at `A`. Invariance of `h` also gives invariance of the section.

The cited declarations are `increasingUnderJointPerm_of_hide`,
`increasingUnderJointPerm_of_hide_invariant`, and `invariantUnderJointPerm_of_hide`.
The map uses one transposition in `S₂`. Its parameter carrier contains a pair of
formal points for every tested index, outcome and parameter. The score stores the two
comparison values on the diagonal and zero off it, with a singleton choice carrier.

Checked: `lake env lean docs/provenance/transfers/249-hiding-fixed-argument.lean`
-/

namespace Transfer249

open AISafetyAtlas.Sovereignty

universe uG uE uF uΩ

abbrev Symmetric (d : ℕ) := Equiv.Perm (Fin d)

structure PrintInstance (d : ℕ) (U : Type uE) (V : Type uF) (W : Type uΩ) where
  E₁ : Set U
  E₂ : Set V
  Θ : Set W
  A : U
  C : V
  n : ℕ
  perms : Fin n → Symmetric d
  score : U → V → W → ℝ

namespace PrintInstance

variable {d U V W} [MulAction (Symmetric d) U] [MulAction (Symmetric d) V]
  [MulAction (Symmetric d) W] (p : PrintInstance d U V W)

def invariantScore : Prop :=
  ∀ i, ∀ S ∈ p.E₁, ∀ D ∈ p.E₂, ∀ θ ∈ p.Θ,
    p.perms i • S ∈ p.E₁ → p.perms i • D ∈ p.E₂ →
    p.score S D θ = p.score (p.perms i • S) (p.perms i • D) (p.perms i • θ)

def hyp : Prop :=
  p.A ∈ p.E₁ ∧ p.C ∈ p.E₂ ∧
  ∀ i, p.perms i • p.A ∈ p.E₁ ∧ p.perms i • p.C = p.C ∧
    Set.MapsTo (fun θ ↦ p.perms i • θ) p.Θ p.Θ ∧
    ∀ θ ∈ p.Θ, p.score p.A p.C θ ≤
      p.score (p.perms i • p.A) (p.perms i • p.C) (p.perms i • θ)

def concl : Prop :=
  IncreasingUnderJointPerm {p.A} p.Θ p.perms (fun S θ ↦ p.score S p.C θ) ∧
  (p.invariantScore →
    InvariantUnderJointPerm {p.A} p.Θ p.perms (fun S θ ↦ p.score S p.C θ))

end PrintInstance

def PrintStatement : Prop :=
  ∀ (d : ℕ) (U : Type uE) (V : Type uF) (W : Type uΩ)
    [MulAction (Symmetric d) U] [MulAction (Symmetric d) V] [MulAction (Symmetric d) W]
    (p : PrintInstance d U V W), p.hyp → p.concl

def LeanStatement : Prop :=
  ∀ {G : Type uG} [Group G] {U : Type uE} [MulAction G U] {V : Type uF} [MulAction G V]
    {W : Type uΩ} [MulAction G W] {n : ℕ} {E : Set U} {Θ : Set W}
    {perms : Fin n → G} {C : V} (h : U → V → W → ℝ), (∀ i, perms i • C = C) →
    ((∀ i, ∀ S ∈ E, ∀ θ ∈ Θ, h S C θ ≤ h (perms i • S) (perms i • C) (perms i • θ)) →
      IncreasingUnderJointPerm E Θ perms (fun S θ ↦ h S C θ)) ∧
    ((∀ i, ∀ S ∈ E, ∀ θ ∈ Θ, h S C θ = h (perms i • S) (perms i • C) (perms i • θ)) →
      InvariantUnderJointPerm E Θ perms (fun S θ ↦ h S C θ)) ∧
    ((∀ (g : G) (S : U) (θ : W), h (g • S) (g • C) (g • θ) = h S C θ) →
      IncreasingUnderJointPerm E Θ perms (fun S θ ↦ h S C θ))

local instance : MulAction (Symmetric 2) (Fin 2) where
  smul g a := g a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

local instance : MulAction (Symmetric 2) Unit where
  smul _ c := c
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

local instance {Q : Type*} : MulAction (Symmetric 2) (Fin 2 × Q) where
  smul g t := (g t.1, t.2)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def phi {Q : Type*} (a b : Q → ℝ) : PrintInstance 2 (Fin 2) Unit (Fin 2 × Q) where
  E₁ := Set.univ
  E₂ := Set.univ
  Θ := Set.univ
  A := 0
  C := ()
  n := 1
  perms _ := Equiv.swap 0 1
  score s _ t := if s = t.1 then (if s = 0 then a t.2 else b t.2) else 0

theorem print_hyp {Q : Type*} {a b : Q → ℝ} (h : ∀ q, a q ≤ b q) : (phi a b).hyp := by
  refine ⟨Set.mem_univ _, Set.mem_univ _, fun i ↦
    ⟨Set.mem_univ _, rfl, fun _ _ ↦ Set.mem_univ _, ?_⟩⟩
  rintro ⟨t, q⟩ _
  change (if (0 : Fin 2) = t then a q else 0) ≤
    (if Equiv.swap (0 : Fin 2) 1 0 = Equiv.swap (0 : Fin 2) 1 t then
      (if Equiv.swap (0 : Fin 2) 1 0 = 0 then a q else b q) else 0)
  by_cases ht : (0 : Fin 2) = t
  · rw [if_pos ht, if_pos (congrArg (Equiv.swap (0 : Fin 2) 1) ht)]
    simpa [Equiv.swap_apply_left] using h q
  · have hs : (Equiv.swap (0 : Fin 2) 1) 0 ≠ (Equiv.swap (0 : Fin 2) 1) t :=
      fun he ↦ ht ((Equiv.swap (0 : Fin 2) 1).injective he)
    rw [if_neg ht, if_neg hs]

theorem invariant_score {Q : Type*} {a b : Q → ℝ} (h : ∀ q, a q = b q) :
    (phi a b).invariantScore := by
  rintro i s _ c _ ⟨t, q⟩ _ _ _
  change (if s = t then (if s = 0 then a q else b q) else 0) =
    (if Equiv.swap (0 : Fin 2) 1 s = Equiv.swap (0 : Fin 2) 1 t then
      (if Equiv.swap (0 : Fin 2) 1 s = 0 then a q else b q) else 0)
  simp [h q]

theorem lean_concl {Q : Type*} {a b : Q → ℝ} (h : (phi a b).concl) :
    (∀ q, a q ≤ b q) ∧ ((∀ q, a q = b q) → ∀ q, a q = b q) := by
  constructor
  · intro q
    have hq := h.1 (0 : Fin 1) 0 (Set.mem_singleton _) (0, q) (Set.mem_univ _)
    change a q ≤ (if (Equiv.swap (0 : Fin 2) 1) 0 = 0 then a q else b q) at hq
    simpa [Equiv.swap_apply_left] using hq
  · intro heq q
    have hq := h.2 (invariant_score heq) (0 : Fin 1) 0 (Set.mem_singleton _) (0, q)
      (Set.mem_univ _)
    change a q = (if (Equiv.swap (0 : Fin 2) 1) 0 = 0 then a q else b q) at hq
    simpa [Equiv.swap_apply_left] using hq

theorem lean_of_print : PrintStatement.{0,0,max uE uΩ} → LeanStatement.{uG,uE,uF,uΩ} := by
  intro h G _ U _ V _ W _ n E Θ perms C score hC
  let Q := Fin n × E × Θ
  let a (q : Q) := score q.2.1 C q.2.2
  let b (q : Q) := score (perms q.1 • (q.2.1 : U)) C (perms q.1 • (q.2.2 : W))
  have increase (hle : ∀ i, ∀ S ∈ E, ∀ θ ∈ Θ,
      score S C θ ≤ score (perms i • S) (perms i • C) (perms i • θ)) :
      IncreasingUnderJointPerm E Θ perms (fun S θ ↦ score S C θ) := by
    have hle' (q : Q) : a q ≤ b q := by
      simpa [a, b, hC] using (hle q.1 q.2.1 q.2.1.property q.2.2 q.2.2.property)
    exact fun i S hS θ hθ ↦ (lean_concl (h 2 _ _ _ (phi a b) (print_hyp hle'))).1
      ⟨i, ⟨S, hS⟩, ⟨θ, hθ⟩⟩
  refine ⟨increase, ?_, fun hinv ↦ increase fun i S _ θ _ ↦ (hinv (perms i) S θ).symm.le⟩
  intro heq
  have heq' (q : Q) : a q = b q := by
    simpa [a, b, hC] using (heq q.1 q.2.1 q.2.1.property q.2.2 q.2.2.property)
  exact fun i S hS θ hθ ↦ (lean_concl
    (h 2 _ _ _ (phi a b) (print_hyp fun q ↦ (heq' q).le))).2 heq' ⟨i, ⟨S, hS⟩, ⟨θ, hθ⟩⟩

theorem print_of_lean : LeanStatement.{0,uE,uF,uΩ} → PrintStatement.{uE,uF,uΩ} := by
  intro h d U V W _ _ _ p hp
  have hl := h (E := {p.A}) (Θ := p.Θ) (perms := p.perms) (C := p.C) p.score
    (fun i ↦ (hp.2.2 i).2.1)
  refine ⟨hl.1 ?_, fun hi ↦ hl.2.1 ?_⟩
  · intro i S hS θ hθ
    rw [Set.mem_singleton_iff.mp hS]
    exact (hp.2.2 i).2.2.2 θ hθ
  · intro i S hS θ hθ
    rw [Set.mem_singleton_iff.mp hS]
    exact hi i p.A hp.1 p.C hp.2.1 θ hθ (hp.2.2 i).1 (by simpa [(hp.2.2 i).2.1] using hp.2.1)

end Transfer249
