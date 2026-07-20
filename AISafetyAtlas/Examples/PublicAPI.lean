module

import AISafetyAtlas

/-!
# Public API compile contract

These anonymous examples exercise the documented facade through the single
root import. They intentionally add no public declarations: their purpose is to
detect accidental renames, missing exports, or leakage of upstream layouts.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Examples.PublicAPI

example (input : ℕ) :
    ¬ComputablePred fun code => (eval code input).Dom :=
  AISafetyAtlas.Computability.halting_problem input

example (input : ℕ) :
    REPred fun code => (eval code input).Dom :=
  AISafetyAtlas.Computability.halting_re input

example (input : ℕ) :
    ¬REPred fun code => ¬(eval code input).Dom :=
  AISafetyAtlas.Computability.nonhalting_not_re input

example (property : Set (ℕ →. ℕ))
    (verifier : ComputablePred fun code => eval code ∈ property)
    {f g : ℕ →. ℕ}
    (computableF : Nat.Partrec f)
    (computableG : Nat.Partrec g)
    (f_mem : f ∈ property) :
    g ∈ property :=
  AISafetyAtlas.Computability.rice property verifier
    computableF computableG f_mem

example (codes : Set Code)
    (extensional : ∀ program₁ program₂,
      eval program₁ = eval program₂ →
      (program₁ ∈ codes ↔ program₂ ∈ codes)) :
    (ComputablePred fun code => code ∈ codes) ↔
      codes = ∅ ∨ codes = Set.univ :=
  AISafetyAtlas.Computability.rice_code_iff codes extensional

example {Alternative : Type} {voterCount : ℕ}
    [NeZero voterCount] [Fintype Alternative]
    (atLeastThree : Fintype.card Alternative ≥ 3) :
    ¬ ∃ rule : AISafetyAtlas.SocialChoice.SocialWelfareFunction
        Alternative voterCount,
      AISafetyAtlas.SocialChoice.Unanimity rule ∧
      AISafetyAtlas.SocialChoice.IndependenceOfIrrelevantAlternatives rule ∧
      AISafetyAtlas.SocialChoice.NonDictatorship rule :=
  AISafetyAtlas.SocialChoice.arrow atLeastThree

example {Alternative : Type} {voterCount : ℕ}
    [NeZero voterCount] [Fintype Alternative]
    (atLeastThree : Fintype.card Alternative ≥ 3) :
    ¬ ∃ rule : AISafetyAtlas.SocialChoice.Utility.SocialWelfareFunction
        Alternative voterCount,
      AISafetyAtlas.SocialChoice.Utility.Unanimity rule ∧
      AISafetyAtlas.SocialChoice.Utility.IndependenceOfIrrelevantAlternatives rule ∧
      AISafetyAtlas.SocialChoice.Utility.NonDictatorship rule :=
  AISafetyAtlas.SocialChoice.Utility.arrow atLeastThree

example {V A : Type} [Fintype V] [Nonempty V] [Fintype A] [Nonempty A]
    (hcardA : 3 ≤ Fintype.card A)
    (f : AISafetyAtlas.SocialChoice.VotingRule)
    (hf_res : AISafetyAtlas.SocialChoice.ResoluteVoting f)
    (hf_unan : AISafetyAtlas.SocialChoice.VotingUnanimity f)
    (hf_sp : AISafetyAtlas.SocialChoice.ResoluteStrategyproofness f hf_res) :
    ∃ d : V, ∀ P : AISafetyAtlas.SocialChoice.VotingProfile V A,
      f P = {AISafetyAtlas.SocialChoice.topChoice P d} :=
  AISafetyAtlas.SocialChoice.gibbard_satterthwaite hcardA f hf_res hf_unan hf_sp

example (property : AISafetyAtlas.Verification.BehavioralProperty)
    (nontrivial : AISafetyAtlas.Verification.Nontrivial property) :
    ¬ AISafetyAtlas.Verification.HasVerifier property :=
  AISafetyAtlas.Verification.rice property nontrivial

example (spec : AISafetyAtlas.Verification.AgentBehavior.SafetySpec)
    (nontrivial : AISafetyAtlas.Verification.AgentBehavior.SpecNontrivial spec) :
    ¬ Nonempty
      (AISafetyAtlas.Verification.AgentBehavior.BehavioralSafetyVerifier spec) :=
  AISafetyAtlas.Verification.AgentBehavior.no_behavioral_safety_verifier
    spec nontrivial

example {Program Scenario Action : Type*} [Primcodable Program]
    (structured : Program → Prop)
    (behavior : Program →
      AISafetyAtlas.Verification.Robot.Behavior Scenario Action)
    (acceptable : Scenario → ℕ → Action → Prop)
    (construction : AISafetyAtlas.Verification.Robot.SwitchingConstruction
      structured behavior acceptable) :
    ¬ Nonempty (AISafetyAtlas.Verification.Robot.Verifier
      structured behavior acceptable) :=
  AISafetyAtlas.Verification.Robot.action_safety_unverifiable
    structured behavior acceptable construction

example {U : Kolmogorov.Map}
    (F : Kolmogorov.FormalSystem U)
    (hU : Kolmogorov.isOptimalConditional U) :
    ∃ x L : ℕ,
      (L : ENat) < Kolmogorov.plainKNat U x ∧
      ¬ F.provable (F.exprKGt x L) :=
  AISafetyAtlas.Logic.chaitin_incompleteness F hU

open LO LO.FirstOrder LO.FirstOrder.Arithmetic in
example (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ δ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ δ ∧ T ⊬ δ :=
  AISafetyAtlas.Logic.godel_first_incompleteness T

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment in
example (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T] :
    T ⊬ ↑T.consistent :=
  AISafetyAtlas.Logic.godel_second_incompleteness T

open LO LO.FirstOrder LO.FirstOrder.Arithmetic in
example :
    ¬∃ τ : ArithmeticSemisentence 1,
      ∀ σ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ σ ↔ ℕ↓[ℒₒᵣ] ⊧ τ/[⌜σ⌝] :=
  AISafetyAtlas.Logic.tarski_undefinability

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment in
example {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence} :
    T ⊢ Bootstrapping.provabilityPred T σ 🡒 σ → T ⊢ σ :=
  AISafetyAtlas.Logic.loeb (T := T) (σ := σ)

example (fs : AISafetyAtlas.Explainability.FeatureIndex)
    (Model : Type)
    (attribution : Fin fs.P → Model → ℝ)
    (hrash : AISafetyAtlas.Explainability.RashomonProperty fs Model attribution)
    (ℓ : Fin fs.L) (j k : Fin fs.P)
    (hj : AISafetyAtlas.Explainability.inGroup fs ℓ j)
    (hk : AISafetyAtlas.Explainability.inGroup fs ℓ k)
    (hjk : j ≠ k)
    (ranking : Fin fs.P → Fin fs.P → Prop)
    (h_faithful : ∀ f : Model,
      ranking j k ↔ attribution j f > attribution k f) :
    False :=
  AISafetyAtlas.Explainability.attribution_impossibility
    fs Model attribution hrash ℓ j k hj hk hjk ranking h_faithful

-- Finite-domain Wolpert–Macready NFL (non-adaptive uniform averaging).
example {X Y : Type*} [Fintype X] [Fintype Y] {m : ℕ}
    (Φ : AISafetyAtlas.Learning.CostPerformance m Y)
    (s₁ s₂ : AISafetyAtlas.Learning.NonadaptiveSchedule X m) :
    AISafetyAtlas.Learning.aggregatePerformance Φ s₁ =
      AISafetyAtlas.Learning.aggregatePerformance Φ s₂ :=
  AISafetyAtlas.Learning.no_free_lunch Φ s₁ s₂

-- Finite-domain Wolpert 1996 supervised NFL (off-training-set form).
example {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (S : Set X)
    (A B : AISafetyAtlas.Learning.SupervisedLearner X Y S) :
    AISafetyAtlas.Learning.aggregateOffTrainingLoss S A =
      AISafetyAtlas.Learning.aggregateOffTrainingLoss S B :=
  AISafetyAtlas.Learning.no_free_lunch_supervised S A B

end AISafetyAtlas.Examples.PublicAPI
