import AISafetyAtlas.Examples.Goodhart.Hackability

/-!
# Skalse et al. footnote 5 as printed is false; the repaired footnote is the one that holds

Joar Skalse, Nikolaus H. R. Howe, Dmitrii Krasheninnikov and David Krueger, *Defining
and Characterizing Reward Hacking*, NeurIPS 2022, §4.2, p. 5, footnote 5 (audit row
S26-R06):

    Consider the case where R₂ is trivial -- then R₁ ⊵ R₂ ⊴ R₃ for any R₁, R₃.

(Transcribed from the page image in
`docs/provenance/printed-statements/skalse-2022-reward-hacking.yaml`, entry
`skalse-fn4-fn5`.) `R₁ ⊵ R₂` says that `R₂` is a simplification of `R₁`, and
Definition 2 on the same page asks of a simplification, besides the two order
clauses, that

    there exist π, π′ ∈ Π such that J₂(π) = J₂(π′) but J₁(π) ≠ J₁(π′).

A trivial `R₂` meets the order clauses against every `R₁`, but this third clause
needs `R₁` to separate two policies. So the footnote fails exactly when `R₁` (or
`R₃`) is itself trivial: there is no distinction for `R₂` to lose. This file proves
that at `R₁ = R₂ = R₃` the constant reward on the library's one-state, two-action
environment (`AISafetyAtlas.Examples.Decision.oneState`, discount one half), which
meets print's standing assumptions of §4.1: finite `S` and `A`, `|A| > 1`, every
state reachable (there is one), finite rewards, `γ ∈ [0, 1]`. The proof uses
nothing about the environment or the policy set beyond the triviality of `R₁`.

Why the repair is the necessary one and not a different theorem:

* it adds only what Definition 2's third clause demands of the base: `R₁` and `R₃`
  are non-trivial on `Π`, and with that the footnote holds for every such pair
  (`AISafetyAtlas.Goodhart.simplifies_of_trivial`);
* the footnote's purpose is untouched: it is offered to show that `R₁ ⊵ R₂ ⊴ R₃`
  does not make `R₁, R₃` unhackable, and the repaired footnote still gives that at
  the library's hackable pair `rewardFalse`, `rewardTrue` (`repaired_inhabited`);
* the library records the same reading at `simplifies_of_trivial`, whose docstring
  says print's "for any `ℛ₁`" fails at a trivial base.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/skalse-footnote-5-literal.lean`. Grading
context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired slips).
-/

open AISafetyAtlas.Goodhart AISafetyAtlas.Decision AISafetyAtlas.Examples.Goodhart
  AISafetyAtlas.Examples.Decision

namespace SkalseFootnoteFiveLiteral

/-- Footnote 5 exactly as printed, in print's setting (finite states and at least
two actions, `γ ≤ 1`): whenever `R₂` is trivial on `Π`, `R₁ ⊵ R₂ ⊴ R₃` for any
`R₁, R₃`, i.e. `R₂` simplifies both `R₁` and `R₃`. -/
def LiteralPrint : Prop :=
  ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nontrivial Action]
    (M : MDP State Action) (I : PMF State) (γ : NNReal), γ ≤ 1 →
    ∀ (Pi : Set (State → PMF Action)) (R₂ : State → Action → ℝ),
      Trivial Pi (J M I γ R₂) →
      ∀ R₁ R₃ : State → Action → ℝ,
        Simplifies Pi (J M I γ R₂) (J M I γ R₁) ∧ Simplifies Pi (J M I γ R₂) (J M I γ R₃)

/-- **The printed footnote is false.** Take `R₁ = R₂ = R₃` the constant reward: it
is trivial, so Definition 2's clause "`J₁(π) ≠ J₁(π′)` for some pair" cannot hold. -/
theorem not_literalPrint : ¬ LiteralPrint := fun h =>
  not_simplifies_of_trivial_base (trivial_rewardConst Set.univ)
    (h Unit Bool oneState startHere half half_lt_one.le Set.univ rewardConst
      (trivial_rewardConst _) rewardConst rewardConst).1

/-- **The repaired footnote holds on the same environment**: a trivial `R₂`
simplifies every `R₁` and `R₃` that separate some pair of policies. -/
theorem repaired_holds (Pi : Set (Unit → PMF Bool)) (R₁ R₂ R₃ : Unit → Bool → ℝ)
    (h₂ : Trivial Pi (J oneState startHere half R₂))
    (h₁ : ∃ π ∈ Pi, ∃ π' ∈ Pi, J oneState startHere half R₁ π ≠ J oneState startHere half R₁ π')
    (h₃ : ∃ π ∈ Pi, ∃ π' ∈ Pi, J oneState startHere half R₃ π ≠ J oneState startHere half R₃ π') :
    Simplifies Pi (J oneState startHere half R₂) (J oneState startHere half R₁) ∧
      Simplifies Pi (J oneState startHere half R₂) (J oneState startHere half R₃) :=
  ⟨simplifies_of_trivial h₂ h₁, simplifies_of_trivial h₂ h₃⟩

/-- The repair is not vacuous, and it keeps the footnote's point: at the hackable
pair `rewardFalse`, `rewardTrue` with the constant reward in the middle,
`R₁ ⊵ R₂ ⊴ R₃` holds and `R₁, R₃` are hackable. -/
theorem repaired_inhabited :
    (Simplifies Set.univ (J oneState startHere half rewardConst)
        (J oneState startHere half rewardFalse) ∧
      Simplifies Set.univ (J oneState startHere half rewardConst)
        (J oneState startHere half rewardTrue)) ∧
    HackableRewards oneState startHere half Set.univ rewardFalse rewardTrue := by
  refine ⟨repaired_holds Set.univ _ _ _ (trivial_rewardConst _)
    ⟨pickFalse, trivial, pickTrue, trivial, ?_⟩ ⟨pickFalse, trivial, pickTrue, trivial, ?_⟩,
    hackable_rewards⟩
  · rw [J_rewardFalse_pickFalse, J_rewardFalse_pickTrue]; norm_num
  · rw [J_rewardTrue_pickFalse, J_rewardTrue_pickTrue]; norm_num

end SkalseFootnoteFiveLiteral
