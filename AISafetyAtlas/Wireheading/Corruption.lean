module

public import AISafetyAtlas.Preference.Regret
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Corrupt-reward no-free-lunch theorem

This module formalizes the algebraic core of Everitt, Krakovna, Orseau, Hutter
and Legg, *Reinforcement Learning with a Corrupted Reward Channel* (IJCAI
2017), Theorem 11.

The paper assumes all true-reward and corruption functions over a uniform
discretization of `[0,1]`.  The proof uses the resulting complement closure:
for every environment `μ`, an observationally indistinguishable `μ⁻` has true
return `horizon - return μ`.  `ComplementedClass` records exactly that
load-bearing consequence together with attained best/worst values.

The proof below pairs the environment witnessing a worst policy's regret with
its complement; the two lower bounds add to that regret directly.  This is the
same complement-pairing mechanism the source uses, carried out from the
recorded consequence rather than from a CRMDP.  The source's own proof is
correct as published; see the retraction note in
`docs/provenance/a1-a3-b1-b3-source-audit.md` for an earlier claim to the
contrary that has been withdrawn.
-/

namespace AISafetyAtlas.Wireheading.Corruption

/-- An environment class closed under complementary reward hypotheses. -/
public structure ComplementedClass (Environment Policy : Type*) where
  returnValue : Environment → Policy → ℝ
  horizon : ℝ
  complement : Environment → Environment
  complement_involutive : Function.Involutive complement
  complement_return :
    ∀ μ π, returnValue μ π + returnValue (complement μ) π = horizon
  bestPolicy : Environment → Policy
  bestPolicy_best :
    ∀ μ π, returnValue μ π ≤ returnValue μ (bestPolicy μ)
  worstEnvironment : Policy → Environment
  worstEnvironment_worst :
    ∀ π μ,
      returnValue μ (bestPolicy μ) - returnValue μ π ≤
        returnValue (worstEnvironment π) (bestPolicy (worstEnvironment π)) -
          returnValue (worstEnvironment π) π
  worstPolicy : Policy
  worstPolicy_worst :
    ∀ π,
      returnValue (worstEnvironment π) (bestPolicy (worstEnvironment π)) -
          returnValue (worstEnvironment π) π ≤
        returnValue (worstEnvironment worstPolicy)
            (bestPolicy (worstEnvironment worstPolicy)) -
          returnValue (worstEnvironment worstPolicy) worstPolicy

/-! ## Definition 10 on an arbitrary class

Everitt et al., IJCAI 2017, Definition 10: *"The regret of `π` is
`Reg(μ, π, s₀, t) = max_{π'} [Ġ_t(μ, π', s₀) − Ġ_t(μ, π, s₀)]`, and the
worst-case regret for a class `ℳ` is `Reg(ℳ, π, s₀, t) = max_{μ ∈ ℳ} Reg(μ, π, s₀, t)`."*

`ComplementedClass.regret` exists only on a class closed under complements.
`regretOf` and `worstCaseRegretOf` are Definition 10 on **any** return function
`G` (print's `Ġ_t` at fixed `s₀, t`) and any class `ℳ` (a set of environments,
so a singleton class is expressible). Print writes `max`, presupposing
attainment; these are real suprema, which are print's maxima wherever the maxima
exist (`regretOf_eq_of_max`, `worstCaseRegretOf_eq_of_max`). At an unattained or
unbounded supremum, or an empty class, the value is Mathlib's junk value and is
not print's.
-/

/-- Definition 10's regret of `π` in `μ`, for any return function `G`. -/
@[expose] public noncomputable def regretOf {Environment Policy : Type*}
    (G : Environment → Policy → ℝ) (μ : Environment) (π : Policy) : ℝ :=
  ⨆ π' : Policy, G μ π' - G μ π

/-- Definition 10's worst-case regret of `π` over a class `ℳ`. -/
@[expose] public noncomputable def worstCaseRegretOf {Environment Policy : Type*}
    (G : Environment → Policy → ℝ) (ℳ : Set Environment) (π : Policy) : ℝ :=
  ⨆ μ : ℳ, regretOf G μ π

/-- Where an optimal policy exists, `regretOf` is print's maximum. -/
public theorem regretOf_eq_of_max {Environment Policy : Type*}
    (G : Environment → Policy → ℝ) (μ : Environment) (π b : Policy)
    (hb : ∀ π', G μ π' ≤ G μ b) :
    regretOf G μ π = G μ b - G μ π := by
  have : Nonempty Policy := ⟨b⟩
  have hle : ∀ π', G μ π' - G μ π ≤ G μ b - G μ π := fun π' => by linarith [hb π']
  exact (ciSup_le hle).antisymm (le_ciSup ⟨_, Set.forall_mem_range.2 hle⟩ b)

/-- Where a worst environment exists in the class, `worstCaseRegretOf` is
print's maximum. -/
public theorem worstCaseRegretOf_eq_of_max {Environment Policy : Type*}
    (G : Environment → Policy → ℝ) (ℳ : Set Environment) (π : Policy) {ν : Environment}
    (hν : ν ∈ ℳ) (hmax : ∀ μ ∈ ℳ, regretOf G μ π ≤ regretOf G ν π) :
    worstCaseRegretOf G ℳ π = regretOf G ν π := by
  have : Nonempty ℳ := ⟨⟨ν, hν⟩⟩
  have hle : ∀ μ : ℳ, regretOf G μ π ≤ regretOf G ν π := fun μ => hmax μ μ.2
  exact (ciSup_le hle).antisymm (le_ciSup ⟨_, Set.forall_mem_range.2 hle⟩ ⟨ν, hν⟩)

namespace ComplementedClass

variable {Environment Policy : Type*}

/-- Regret in one environment (Everitt et al., Definition 10). -/
@[expose] public def regret (M : ComplementedClass Environment Policy)
    (μ : Environment) (π : Policy) : ℝ :=
  M.returnValue μ (M.bestPolicy μ) - M.returnValue μ π

/-- Worst-case regret, with its maximum explicitly witnessed. -/
@[expose] public def worstCaseRegret
    (M : ComplementedClass Environment Policy) (π : Policy) : ℝ :=
  M.regret (M.worstEnvironment π) π

/-- The complemented-class regret is Definition 10's regret of its return. -/
public theorem regret_eq_regretOf (M : ComplementedClass Environment Policy)
    (μ : Environment) (π : Policy) :
    M.regret μ π = regretOf M.returnValue μ π :=
  (regretOf_eq_of_max _ μ π _ (M.bestPolicy_best μ)).symm

/-- The complemented-class worst-case regret is Definition 10's worst-case
regret over the whole class. -/
public theorem worstCaseRegret_eq_worstCaseRegretOf
    (M : ComplementedClass Environment Policy) (π : Policy) :
    M.worstCaseRegret π = worstCaseRegretOf M.returnValue Set.univ π := by
  rw [worstCaseRegretOf_eq_of_max _ _ π (Set.mem_univ (M.worstEnvironment π))
    (fun μ _ => by
      rw [← M.regret_eq_regretOf, ← M.regret_eq_regretOf]
      exact M.worstEnvironment_worst π μ),
    ← M.regret_eq_regretOf]
  rfl

/--
**Everitt et al. Theorem 11 (complement-closure core).**

Every policy has at least half the worst-case regret of a worst policy.
-/
public theorem everitt_theorem_eleven
    (M : ComplementedClass Environment Policy) (π : Policy) :
    M.worstCaseRegret M.worstPolicy / 2 ≤ M.worstCaseRegret π := by
  let μ := M.worstEnvironment M.worstPolicy
  have hμ : M.regret μ π ≤ M.worstCaseRegret π :=
    M.worstEnvironment_worst π μ
  have hμc : M.regret (M.complement μ) π ≤ M.worstCaseRegret π :=
    M.worstEnvironment_worst π (M.complement μ)
  have hbest :
      M.returnValue (M.complement μ) M.worstPolicy -
          M.returnValue (M.complement μ) π ≤
        M.regret (M.complement μ) π := by
    dsimp only [regret]
    linarith [M.bestPolicy_best (M.complement μ) M.worstPolicy]
  have hcomplementPolicy := M.complement_return μ π
  have hcomplementWorst := M.complement_return μ M.worstPolicy
  dsimp only [worstCaseRegret, regret] at hμ hμc hbest ⊢
  dsimp only [μ] at hμ hμc hbest hcomplementPolicy hcomplementWorst ⊢
  linarith

/-- Forget the return-level structure, retaining the generic regret interface. -/
public def toRegretModel (M : ComplementedClass Environment Policy) :
    AISafetyAtlas.Preference.RegretModel Environment Policy where
  regret := M.regret
  worstCaseRegret := M.worstCaseRegret
  worstCaseRegret_upper := fun R π => M.worstEnvironment_worst π R
  worstCaseRegret_attained := fun π => ⟨M.worstEnvironment π, rfl⟩
  worstPolicy := M.worstPolicy
  worstPolicy_worst := M.worstPolicy_worst

/-- Package the concrete BY-039 proof for the BY-011 regret bridge. -/
public theorem halfMaximalRegretBound
    (M : ComplementedClass Environment Policy) :
    AISafetyAtlas.Preference.HalfMaximalRegretBound M.toRegretModel :=
  ⟨M.everitt_theorem_eleven⟩

end ComplementedClass
end AISafetyAtlas.Wireheading.Corruption
