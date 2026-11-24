module

public import AISafetyAtlas.Verification.AgentBehavior

/-!
# A non-trivial judge, and Melo et al.'s undecidability fired at it

Witnesses the hypotheses of
`AISafetyAtlas.Verification.AgentBehavior.judgeSpec_nontrivial` with the judge
`J(i, o) = [o = i]`: it rejects `(0, 1)`, and every input `i` has the accepted
output `o⁺ = i`. Print's non-triviality of the property then follows, and
`no_behavioral_safety_verifier` fires at the property the judge defines.

The identity judge is the instance the audit's defect note used; it shows the
hypotheses are inhabited, not that alignment is equality.
-/

open Nat.Partrec (Code)

namespace AISafetyAtlas.Examples.Verification.AgentBehavior

open AISafetyAtlas.Verification.AgentBehavior

/-- The judge accepting exactly the output equal to the input. -/
public def echoJudge : Judge := fun i o => decide (o = i)

private theorem computable_echoJudge : Computable₂ echoJudge :=
  (Primrec.eq.comp Primrec.snd Primrec.fst).decide.to_comp

private theorem echoJudge_nontrivial : JudgeNontrivial echoJudge :=
  ⟨⟨0, 1, by decide⟩, fun i => ⟨i, by simp [echoJudge]⟩⟩

/-- **Print's judge layer is inhabited**: a computable, non-trivial judge whose
property is non-trivial. -/
public theorem echoJudge_spec_nontrivial : SpecNontrivial (judgeSpec echoJudge) :=
  judgeSpec_nontrivial echoJudge computable_echoJudge echoJudge_nontrivial

/-- **Melo et al.'s claim at a judge**: no total computable verifier decides the
property a computable non-trivial judge defines. -/
public theorem no_verifier_for_echoJudge :
    ¬ Nonempty (BehavioralSafetyVerifier (judgeSpec echoJudge)) :=
  no_behavioral_safety_verifier _ echoJudge_spec_nontrivial

/-- **Print's halting reduction at the echo judge**: a computable `M ↦ M′`
reducing halting at input `0` to the judge's property or to its complement. -/
public theorem halting_reduces_to_echoJudge :
    ∃ f : Agent → Agent, Computable f ∧
      ((∀ M, Satisfies (judgeSpec echoJudge) (f M) ↔ (Nat.Partrec.Code.eval M 0).Dom) ∨
        (∀ M, ¬ Satisfies (judgeSpec echoJudge) (f M) ↔ (Nat.Partrec.Code.eval M 0).Dom)) :=
  AISafetyAtlas.Verification.AgentBehavior.halting_reduces_to_spec _
    echoJudge_spec_nontrivial 0

/-- **Print's second route, run to its contradiction**: a verifier for the echo
judge's property, composed with the reduction, would decide halting at `0`. -/
example : ¬ Nonempty (BehavioralSafetyVerifier (judgeSpec echoJudge)) := by
  rintro ⟨v⟩
  obtain ⟨f, hf, hred⟩ := halting_reduces_to_echoJudge
  rcases hred with hred | hred
  · refine AISafetyAtlas.Computability.halting_problem 0
      (ComputablePred.computable_iff.mpr ⟨fun M => v.decide (f M),
        v.computable_decide.comp hf, ?_⟩)
    funext M
    exact propext ((v.correct (f M)).trans (hred M)).symm
  · refine AISafetyAtlas.Computability.halting_problem 0
      (ComputablePred.computable_iff.mpr ⟨fun M => !v.decide (f M),
        Primrec.not.to_comp.comp (v.computable_decide.comp hf), ?_⟩)
    funext M
    have h := (v.correct (f M)).not.trans (hred M)
    apply propext
    rw [← h]
    simp

/-- `halting_reduces_to_spec_of_none_not_mem` at the echo judge's property: it is
non-trivial and excludes the nowhere-defined function. -/
example : ∃ f : Agent → Agent, Computable f ∧
    ∀ M, Satisfies (judgeSpec echoJudge) (f M) ↔ (Nat.Partrec.Code.eval M 0).Dom :=
  AISafetyAtlas.Verification.AgentBehavior.halting_reduces_to_spec_of_none_not_mem _
    echoJudge_spec_nontrivial (none_not_mem_judgeSpec echoJudge) 0

/-- **Print's literal `M′` at the echo judge** (library reading, `judgeSpec`): `M′`
has the property exactly when `M` halts on `0`. -/
public theorem halting_reduces_to_echoJudge_literal :
    ∃ f : Agent → Agent, Computable f ∧
      ∀ M, Satisfies (judgeSpec echoJudge) (f M) ↔ (Nat.Partrec.Code.eval M 0).Dom :=
  AISafetyAtlas.Verification.AgentBehavior.halting_reduces_to_judgeSpec echoJudge
    computable_echoJudge echoJudge_nontrivial 0

/-- Under the other reading the echo judge's property contains the nowhere-defined
behaviour. -/
public theorem none_mem_echoJudge_outputs :
    (fun _ => Part.none : ℕ →. ℕ) ∈ judgeSpecOutputs echoJudge :=
  AISafetyAtlas.Verification.AgentBehavior.none_mem_judgeSpecOutputs echoJudge

/-- Failing the echo judge's property under the other reading is r.e. -/
public theorem echoJudge_outputs_compl_re :
    REPred fun M : Agent => ¬ Satisfies (judgeSpecOutputs echoJudge) M :=
  AISafetyAtlas.Verification.AgentBehavior.judgeSpecOutputs_compl_re echoJudge
    computable_echoJudge

/-- `not_exists_halting_reduction_of_compl_re` at the echo judge's property under
the other reading. -/
example : ¬ ∃ f : Agent → Agent, Computable f ∧
    ∀ M, Satisfies (judgeSpecOutputs echoJudge) (f M) ↔ (Nat.Partrec.Code.eval M 0).Dom :=
  AISafetyAtlas.Verification.AgentBehavior.not_exists_halting_reduction_of_compl_re _ 0
    echoJudge_outputs_compl_re

/-- **Print's literal `M′` fails at the echo judge under the other reading**
(`judgeSpecOutputs`): no computable `M ↦ M′` has the property exactly when `M`
halts on `0`. -/
public theorem no_literal_reduction_echoJudge_outputs :
    ¬ ∃ f : Agent → Agent, Computable f ∧
      ∀ M, Satisfies (judgeSpecOutputs echoJudge) (f M) ↔ (Nat.Partrec.Code.eval M 0).Dom :=
  AISafetyAtlas.Verification.AgentBehavior.not_exists_halting_reduction_judgeSpecOutputs
    echoJudge computable_echoJudge 0

end AISafetyAtlas.Examples.Verification.AgentBehavior
