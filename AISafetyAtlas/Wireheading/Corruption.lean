module

public import AISafetyAtlas.Preference.Regret
public import Mathlib.Tactic.Linarith

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
