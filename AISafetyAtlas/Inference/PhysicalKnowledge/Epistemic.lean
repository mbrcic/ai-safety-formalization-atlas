module

public import AISafetyAtlas.Inference.PhysicalKnowledge

/-!
# Epistemic consequences of physical knowledge — Wolpert 2018

This module continues the source-faithful physical-knowledge layer with the
Boolean consequences in Corollaries 20 and 21 and the two-device impossibilities
in Corollaries 23 and 24 of D. H. Wolpert, *Constraints on physical reality
arising from a formalization of knowledge* (2018), section V.1. Corollary 24's
earlier Corollary 3 engine is exposed rather than assumed.

The source's Corollary 21(ii) is not true as printed. Its second disjunct assumes
that `Γ₁ ⇒ Γ₂` is true and that the device knows `Γ₁ ⇒ Γ₃`, then concludes that
`Γ₂ ⇒ Γ₃` is true. The Boolean valuation `Γ₁ = false`, `Γ₂ = true`,
`Γ₃ = false` refutes that implication even when the knowledge premise is
inhabited. The intended weakening of Corollary 20(iii) is recorded below as
`corollary21_ii_repaired`: one implication is known and the other is true, and
the conclusion is the composite implication `Γ₁ ⇒ Γ₃`.

## Primary surface

| Source | Declaration | Content |
|---|---|---|
| Eq. (9) | `boolImplies`, `Implies` | Material implication on Boolean functions |
| Corollary 20(i–iii) | `corollary20_i`, `corollary20_ii`, `corollary20_iii` | Truth-preserving implications under the printed refinement hypotheses |
| Corollary 20(iv) | `corollary20_iv` | Finite implication chains |
| Corollary 21(i) | `corollary21_i` | One known premise and one true premise suffice |
| repaired Corollary 21(ii) | `corollary21_ii_repaired` | The valid weakening of Corollary 20(iii) |
| Corollary 3 | `exists_three_inequivalent_not_weaklyInfers` | Three inequivalent binary functions missed by one of two devices |
| Corollary 23 | `corollary23` | One of two distinguishable devices never knows the other's conclusion |
| Corollary 24 | `corollary24` | Knowledge of one conclusion forces three unknown targets for the other device |

The failure of the printed Corollary 21(ii), and the paper's Example 9 failure
of the distribution axiom, have executable certificates in
`AISafetyAtlas.Examples.Inference.PhysicalKnowledge.Epistemic`.
-/

namespace AISafetyAtlas.Inference

universe u v v'

variable {U : Type u}

/-- Equation (9): material implication on the source's two truth values. -/
@[expose] public def boolImplies (p q : Bool) : Bool :=
  !p || q

/-- Pointwise material implication between Boolean-valued functions. -/
public abbrev Implies (Γ₁ Γ₂ : U → Bool) : U → Bool :=
  fun u => boolImplies (Γ₁ u) (Γ₂ u)

/-- A Boolean-valued function is true throughout the context `W`. -/
@[expose] public def TrueOn (W : Set U) (Γ : U → Bool) : Prop :=
  ∀ u : U, u ∈ W → Γ u = true

private theorem consequent_true {p q : Bool}
    (hp : p = true) (himp : boolImplies p q = true) : q = true := by
  cases p <;> cases q <;> simp [boolImplies] at hp himp ⊢

private theorem implication_trans {p q r : Bool}
    (hpq : boolImplies p q = true) (hqr : boolImplies q r = true) :
    boolImplies p r = true := by
  cases p <;> cases q <;> cases r <;> simp [boolImplies] at hpq hqr ⊢

/-- **Corollary 20(i).** Knowledge that `Γ₁` is true, together with truth of
`Γ₁ ⇒ Γ₂`, makes `Γ₂` true. Only `Γ₁` must be refined by `W`. -/
public theorem corollary20_i
    {C : InferenceDevice.{u, v} U} {Γ₁ Γ₂ : U → Bool} {W : Set U}
    (href₁ : RefinesOn W Γ₁)
    (hknow₁ : PhysicallyKnows C Γ₁ true W)
    (himp : TrueOn W (Implies Γ₁ Γ₂)) :
    TrueOn W Γ₂ := by
  intro u hu
  exact consequent_true
    (true_on_of_physicallyKnows_true href₁ hknow₁ u hu)
    (himp u hu)

/-- **Corollary 20(ii).** If the antecedent and its implication are both known
true under their respective refinement hypotheses, the consequent is true. -/
public theorem corollary20_ii
    {C : InferenceDevice.{u, v} U} {Γ₁ Γ₂ : U → Bool} {W : Set U}
    (href₁ : RefinesOn W Γ₁) (hrefImp : RefinesOn W (Implies Γ₁ Γ₂))
    (hknow₁ : PhysicallyKnows C Γ₁ true W)
    (hknowImp : PhysicallyKnows C (Implies Γ₁ Γ₂) true W) :
    TrueOn W Γ₂ :=
  corollary20_i href₁ hknow₁
    (true_on_of_physicallyKnows_true hrefImp hknowImp)

/-- **Corollary 20(iii).** Knowledge of two successive implications makes the
composite implication true. No refinement of the three component functions is
assumed. -/
public theorem corollary20_iii
    {C : InferenceDevice.{u, v} U} {Γ₁ Γ₂ Γ₃ : U → Bool} {W : Set U}
    (href₁₂ : RefinesOn W (Implies Γ₁ Γ₂))
    (href₂₃ : RefinesOn W (Implies Γ₂ Γ₃))
    (hknow₁₂ : PhysicallyKnows C (Implies Γ₁ Γ₂) true W)
    (hknow₂₃ : PhysicallyKnows C (Implies Γ₂ Γ₃) true W) :
    TrueOn W (Implies Γ₁ Γ₃) := by
  intro u hu
  exact implication_trans
    (true_on_of_physicallyKnows_true href₁₂ hknow₁₂ u hu)
    (true_on_of_physicallyKnows_true href₂₃ hknow₂₃ u hu)

/-- **Corollary 20(iv), zero-indexed.** A known base fact and a finite chain of
known implications make every fact through index `n` true. The source indexes
the same chain from `1` through `N`. -/
public theorem corollary20_iv
    {C : InferenceDevice.{u, v} U} (Γ : ℕ → U → Bool) (W : Set U) (n : ℕ)
    (href₀ : RefinesOn W (Γ 0))
    (hknow₀ : PhysicallyKnows C (Γ 0) true W)
    (hrefStep : ∀ i : ℕ, i < n → RefinesOn W (Implies (Γ i) (Γ (i + 1))))
    (hknowStep : ∀ i : ℕ, i < n →
      PhysicallyKnows C (Implies (Γ i) (Γ (i + 1))) true W) :
    ∀ i : ℕ, i ≤ n → TrueOn W (Γ i) := by
  intro i hi
  induction i with
  | zero => exact true_on_of_physicallyKnows_true href₀ hknow₀
  | succ i ih =>
      have hin : i < n := Nat.lt_of_succ_le hi
      have hprev : TrueOn W (Γ i) := ih (Nat.le_of_lt hin)
      have himp : TrueOn W (Implies (Γ i) (Γ (i + 1))) :=
        true_on_of_physicallyKnows_true (hrefStep i hin) (hknowStep i hin)
      intro u hu
      exact consequent_true (hprev u hu) (himp u hu)

/-- **Corollary 21(i).** It suffices for either the antecedent or the
implication to be physically known, provided the other is true. -/
public theorem corollary21_i
    {C : InferenceDevice.{u, v} U} {Γ₁ Γ₂ : U → Bool} {W : Set U}
    (href₁ : RefinesOn W Γ₁) (hrefImp : RefinesOn W (Implies Γ₁ Γ₂))
    (h :
      (PhysicallyKnows C Γ₁ true W ∧ TrueOn W (Implies Γ₁ Γ₂)) ∨
      (TrueOn W Γ₁ ∧ PhysicallyKnows C (Implies Γ₁ Γ₂) true W)) :
    TrueOn W Γ₂ := by
  rcases h with ⟨hknow, himp⟩ | ⟨htrue, hknow⟩
  · exact corollary20_i href₁ hknow himp
  · intro u hu
    exact consequent_true (htrue u hu)
      (true_on_of_physicallyKnows_true hrefImp hknow u hu)

/-- **Repair of Corollary 21(ii).** This is the valid weakening of Corollary
20(iii): one successive implication is known and the other is true, so the
*composite* implication is true. The printed second disjunct and conclusion do
not state this and are refuted by an executable model. -/
public theorem corollary21_ii_repaired
    {C : InferenceDevice.{u, v} U} {Γ₁ Γ₂ Γ₃ : U → Bool} {W : Set U}
    (href₁₂ : RefinesOn W (Implies Γ₁ Γ₂))
    (href₂₃ : RefinesOn W (Implies Γ₂ Γ₃))
    (h :
      (PhysicallyKnows C (Implies Γ₁ Γ₂) true W ∧
        TrueOn W (Implies Γ₂ Γ₃)) ∨
      (TrueOn W (Implies Γ₁ Γ₂) ∧
        PhysicallyKnows C (Implies Γ₂ Γ₃) true W)) :
    TrueOn W (Implies Γ₁ Γ₃) := by
  rcases h with ⟨hknow, htrue⟩ | ⟨htrue, hknow⟩
  · intro u hu
    exact implication_trans
      (true_on_of_physicallyKnows_true href₁₂ hknow u hu) (htrue u hu)
  · intro u hu
    exact implication_trans (htrue u hu)
      (true_on_of_physicallyKnows_true href₂₃ hknow u hu)

/-- Weak inference is invariant under Boolean negation of the target. -/
public theorem weaklyInfers_not_iff (C : InferenceDevice.{u, v} U)
    (Γ : U → Bool) :
    WeaklyInfers C (fun u => !(Γ u)) ↔ WeaklyInfers C Γ := by
  constructor
  · intro h γ f hf hγ
    let f' : Bool → Bool := fun b => f (!b)
    have hf' : IsProbe f' (!γ) := by
      intro b
      simp only [f']
      rw [hf]
      cases b <;> cases γ <;> decide
    obtain ⟨wγ, hwγ⟩ := hγ
    obtain ⟨x, hx, hrun⟩ := h (!γ) f' hf'
      ⟨wγ, by simp [hwγ]⟩
    refine ⟨x, hx, fun w hw => ?_⟩
    simpa [f'] using hrun w hw
  · intro h γ f hf hγ
    let f' : Bool → Bool := fun b => f (!b)
    have hf' : IsProbe f' (!γ) := by
      intro b
      simp only [f']
      rw [hf]
      cases b <;> cases γ <;> decide
    obtain ⟨wγ, hwγ⟩ := hγ
    obtain ⟨x, hx, hrun⟩ := h (!γ) f' hf'
      ⟨wγ, by simpa using congrArg Bool.not hwγ⟩
    refine ⟨x, hx, fun w hw => ?_⟩
    simpa [f'] using hrun w hw

/-! ## Function partitions and the three-function gap -/

/-- Two functions are equivalent in the paper's sense when they induce the same
partition of `U`. Their codomains need not agree. -/
@[expose] public def FunctionallyEquivalent {A : Type v} {B : Type v'}
    (Γ : U → A) (Δ : U → B) : Prop :=
  ∀ u w : U, Γ u = Γ w ↔ Δ u = Δ w

private theorem functionallyEquivalent_of_eq
    {Γ Δ : U → Bool} (h : ∀ u, Γ u = Δ u) :
    FunctionallyEquivalent Γ Δ := by
  intro u w
  rw [h u, h w]

private theorem functionallyEquivalent_of_eq_not
    {Γ Δ : U → Bool} (h : ∀ u, Γ u = !(Δ u)) :
    FunctionallyEquivalent Γ Δ := by
  intro u w
  rw [h u, h w]
  simp

/-- A realized joint cell that has a neighbour along each coordinate. Its
singleton indicator therefore defines a third partition, inequivalent to either
coordinate partition. -/
private structure JointCorner (A B : U → Bool) where
  center : U
  sameA : U
  sameB : U
  A_same : A center = A sameA
  B_diff : B center ≠ B sameA
  B_same : B center = B sameB
  A_diff : A center ≠ A sameB

private theorem exists_jointCorner (A B : U → Bool)
    (hA : Function.Surjective A) (hB : Function.Surjective B)
    (hneq : ¬ FunctionallyEquivalent A B) :
    Nonempty (JointCorner A B) := by
  classical
  let At : Bool → Bool → Prop := fun a b => ∃ u, A u = a ∧ B u = b
  by_cases h00 : At false false
  · obtain ⟨u00, hu00A, hu00B⟩ := h00
    by_cases h01 : At false true
    · obtain ⟨u01, hu01A, hu01B⟩ := h01
      by_cases h10 : At true false
      · obtain ⟨u10, hu10A, hu10B⟩ := h10
        exact ⟨⟨u00, u01, u10,
          hu00A.trans hu01A.symm,
          by rw [hu00B, hu01B]; decide,
          hu00B.trans hu10B.symm,
          by rw [hu00A, hu10A]; decide⟩⟩
      · have h11 : At true true := by
          obtain ⟨u, huA⟩ := hA true
          cases huB : B u
          · exact (h10 ⟨u, huA, huB⟩).elim
          · exact ⟨u, huA, huB⟩
        obtain ⟨u11, hu11A, hu11B⟩ := h11
        exact ⟨⟨u01, u00, u11,
          hu01A.trans hu00A.symm,
          by rw [hu01B, hu00B]; decide,
          hu01B.trans hu11B.symm,
          by rw [hu01A, hu11A]; decide⟩⟩
    · have h11 : At true true := by
        obtain ⟨u, huB⟩ := hB true
        cases huA : A u
        · exact (h01 ⟨u, huA, huB⟩).elim
        · exact ⟨u, huA, huB⟩
      obtain ⟨u11, hu11A, hu11B⟩ := h11
      have h10 : At true false := by
        by_contra hn10
        apply hneq
        apply functionallyEquivalent_of_eq
        intro u
        cases huA : A u <;> cases huB : B u
        · rfl
        · exact (h01 ⟨u, huA, huB⟩).elim
        · exact (hn10 ⟨u, huA, huB⟩).elim
        · rfl
      obtain ⟨u10, hu10A, hu10B⟩ := h10
      exact ⟨⟨u10, u11, u00,
        hu10A.trans hu11A.symm,
        by rw [hu10B, hu11B]; decide,
        hu10B.trans hu00B.symm,
        by rw [hu10A, hu00A]; decide⟩⟩
  · have h01 : At false true := by
      obtain ⟨u, huA⟩ := hA false
      cases huB : B u
      · exact (h00 ⟨u, huA, huB⟩).elim
      · exact ⟨u, huA, huB⟩
    have h10 : At true false := by
      obtain ⟨u, huB⟩ := hB false
      cases huA : A u
      · exact (h00 ⟨u, huA, huB⟩).elim
      · exact ⟨u, huA, huB⟩
    obtain ⟨u01, hu01A, hu01B⟩ := h01
    obtain ⟨u10, hu10A, hu10B⟩ := h10
    have h11 : At true true := by
      by_contra hn11
      apply hneq
      apply functionallyEquivalent_of_eq_not
      intro u
      cases huA : A u <;> cases huB : B u
      · exact (h00 ⟨u, huA, huB⟩).elim
      · rfl
      · rfl
      · exact (hn11 ⟨u, huA, huB⟩).elim
    obtain ⟨u11, hu11A, hu11B⟩ := h11
    exact ⟨⟨u11, u10, u01,
      hu11A.trans hu10A.symm,
      by rw [hu11B, hu10B]; decide,
      hu11B.trans hu01B.symm,
      by rw [hu11A, hu01A]; decide⟩⟩

private noncomputable def jointCornerIndicator
    {A B : U → Bool} (J : JointCorner A B) : U → Bool :=
  fun u => decide (A u = A J.center ∧ B u = B J.center)

private theorem jointCornerIndicator_surjective
    {A B : U → Bool} (J : JointCorner A B) :
    Function.Surjective (jointCornerIndicator J) := by
  intro b
  cases b
  · exact ⟨J.sameA, by
      simp [jointCornerIndicator, J.A_same.symm, J.B_diff.symm]⟩
  · exact ⟨J.center, by simp [jointCornerIndicator]⟩

private theorem jointCornerIndicator_inequivalent_left
    {A B : U → Bool} (J : JointCorner A B) :
    ¬ FunctionallyEquivalent (jointCornerIndicator J) A := by
  intro h
  have heq := (h J.center J.sameA).mpr J.A_same
  have hcell :
      A J.sameA = A J.center ∧ B J.sameA = B J.center := by
    simpa [jointCornerIndicator] using heq
  exact J.B_diff hcell.2.symm

private theorem jointCornerIndicator_inequivalent_right
    {A B : U → Bool} (J : JointCorner A B) :
    ¬ FunctionallyEquivalent (jointCornerIndicator J) B := by
  intro h
  have heq := (h J.center J.sameB).mpr J.B_same
  have hcell :
      A J.sameB = A J.center ∧ B J.sameB = B J.center := by
    simpa [jointCornerIndicator] using heq
  exact J.A_diff hcell.1.symm

private theorem not_weaklyInfers_jointCornerIndicator
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hdist : Distinguishable C₁ C₂) (h₂₁ : InfersDevice C₂ C₁)
    (J : JointCorner C₁.concl C₂.concl) :
    ¬ WeaklyInfers C₁ (jointCornerIndicator J) := by
  intro h
  obtain ⟨waT, hwaT⟩ := C₁.concl_surjective true
  obtain ⟨xEq, hxEq, hEq⟩ := h₂₁ true id isProbe_id ⟨waT, hwaT⟩
  obtain ⟨waF, hwaF⟩ := C₁.concl_surjective false
  obtain ⟨xNe, hxNe, hNe⟩ := h₂₁ false (fun b => !b) isProbe_not ⟨waF, hwaF⟩
  have hsurj := jointCornerIndicator_surjective J
  cases ha : C₁.concl J.center <;> cases hb : C₂.concl J.center
  · obtain ⟨wT, hwT⟩ := hsurj true
    obtain ⟨x₁, hx₁, hrun⟩ := h true id isProbe_id ⟨wT, hwT⟩
    obtain ⟨w, hw₁, hw₂⟩ := hdist x₁ hx₁ xEq hxEq
    have e₁ := hrun w hw₁
    have e₂ := hEq w hw₂
    cases hAw : C₁.concl w <;> cases hBw : C₂.concl w <;>
      simp [jointCornerIndicator, ha, hb, hAw, hBw] at e₁ e₂
  · obtain ⟨wT, hwT⟩ := hsurj true
    obtain ⟨x₁, hx₁, hrun⟩ := h true id isProbe_id ⟨wT, hwT⟩
    obtain ⟨w, hw₁, hw₂⟩ := hdist x₁ hx₁ xNe hxNe
    have e₁ := hrun w hw₁
    have e₂ := hNe w hw₂
    cases hAw : C₁.concl w <;> cases hBw : C₂.concl w <;>
      simp [jointCornerIndicator, ha, hb, hAw, hBw] at e₁ e₂
  · obtain ⟨wF, hwF⟩ := hsurj false
    obtain ⟨x₁, hx₁, hrun⟩ := h false (fun b => !b) isProbe_not ⟨wF, hwF⟩
    obtain ⟨w, hw₁, hw₂⟩ := hdist x₁ hx₁ xNe hxNe
    have e₁ := hrun w hw₁
    have e₂ := hNe w hw₂
    cases hAw : C₁.concl w <;> cases hBw : C₂.concl w <;>
      simp [jointCornerIndicator, ha, hb, hAw, hBw] at e₁ e₂
  · obtain ⟨wF, hwF⟩ := hsurj false
    obtain ⟨x₁, hx₁, hrun⟩ := h false (fun b => !b) isProbe_not ⟨wF, hwF⟩
    obtain ⟨w, hw₁, hw₂⟩ := hdist x₁ hx₁ xEq hxEq
    have e₁ := hrun w hw₁
    have e₂ := hEq w hw₂
    cases hAw : C₁.concl w <;> cases hBw : C₂.concl w <;>
      simp [jointCornerIndicator, ha, hb, hAw, hBw] at e₁ e₂

/-- **Wolpert 2018, Corollary 3.** If `C₂` infers the distinguishable device
`C₁`, and their conclusion partitions differ, then `C₁` fails to infer at least
three pairwise-inequivalent surjective Boolean functions.

The third function is the indicator of a realized joint conclusion cell that
has a neighbour along both Boolean coordinates. -/
public theorem exists_three_inequivalent_not_weaklyInfers
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hdist : Distinguishable C₁ C₂)
    (hneq : ¬ FunctionallyEquivalent C₁.concl C₂.concl)
    (h₂₁ : InfersDevice C₂ C₁) :
    ∃ Γ₀ Γ₁ Γ₂ : U → Bool,
      Function.Surjective Γ₀ ∧ Function.Surjective Γ₁ ∧ Function.Surjective Γ₂ ∧
      ¬ FunctionallyEquivalent Γ₀ Γ₁ ∧
      ¬ FunctionallyEquivalent Γ₀ Γ₂ ∧
      ¬ FunctionallyEquivalent Γ₁ Γ₂ ∧
      ¬ WeaklyInfers C₁ Γ₀ ∧ ¬ WeaklyInfers C₁ Γ₁ ∧ ¬ WeaklyInfers C₁ Γ₂ := by
  classical
  obtain ⟨J⟩ := exists_jointCorner C₁.concl C₂.concl
    C₁.concl_surjective C₂.concl_surjective hneq
  refine ⟨C₁.concl, C₂.concl, jointCornerIndicator J,
    C₁.concl_surjective, C₂.concl_surjective,
    jointCornerIndicator_surjective J, hneq, ?_, ?_,
    not_weaklyInfers_own_concl C₁, ?_,
    not_weaklyInfers_jointCornerIndicator hdist h₂₁ J⟩
  · intro heq
    exact jointCornerIndicator_inequivalent_left J
      (fun u w => (heq u w).symm)
  · intro heq
    exact jointCornerIndicator_inequivalent_right J
      (fun u w => (heq u w).symm)
  · intro h₁₂
    exact not_infersDevice_both_of_distinguishable hdist h₁₂ h₂₁

/-- **Corollary 23.** For two distinguishable devices, at least one device
physically knows no realized value of the other's conclusion over any context.
This is Proposition 2 transported through physical knowledge ⇒ weak inference. -/
public theorem corollary23
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hdist : Distinguishable C₁ C₂) :
    (∀ (W : Set U) (γ : Bool), ¬ PhysicallyKnows C₁ C₂.concl γ W) ∨
    (∀ (W : Set U) (γ : Bool), ¬ PhysicallyKnows C₂ C₁.concl γ W) := by
  classical
  by_cases h₁₂ : ∃ (W : Set U) (γ : Bool), PhysicallyKnows C₁ C₂.concl γ W
  · right
    rintro W₂ γ₂ h₂₁
    obtain ⟨W₁, γ₁, h₁₂'⟩ := h₁₂
    exact not_infersDevice_both_of_distinguishable hdist
      h₁₂'.weaklyInfers h₂₁.weaklyInfers
  · left
    intro W γ h
    exact h₁₂ ⟨W, γ, h⟩

/-- **Wolpert 2018, Corollary 24.** Suppose distinguishable devices have
inequivalent conclusions and `C₂` physically knows a value of `C₁`'s
conclusion over a context that refines that conclusion. Then there are three
pairwise-inequivalent surjective binary targets that `C₁` cannot physically
know on any context refining the respective target.

The proof exposes the source's dependency on Corollary 3: physical knowledge
gives `C₂ > C₁`, Corollary 3 supplies three targets not weakly inferred by
`C₁`, and Definition 11 implies weak inference.

`_href` is the source's *"there is a `W ⊆ U` that refines `Y`"*, kept so the
signature is the printed one, and unused: only the knowledge of `C₁.concl`
matters, and it already gives `C₂ > C₁`. `scripts/minimize_hypotheses.py` reports
it `REMOVABLE`. The refinement hypotheses inside the conclusion are likewise not
needed, and are kept for the same reason. -/
public theorem corollary24
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    {W : Set U} {γ : Bool}
    (hdist : Distinguishable C₁ C₂)
    (hneq : ¬ FunctionallyEquivalent C₁.concl C₂.concl)
    (_href : RefinesOn W C₁.concl)
    (hknow : PhysicallyKnows C₂ C₁.concl γ W) :
    ∃ Γ₀ Γ₁ Γ₂ : U → Bool,
      Function.Surjective Γ₀ ∧ Function.Surjective Γ₁ ∧
      Function.Surjective Γ₂ ∧
      ¬ FunctionallyEquivalent Γ₀ Γ₁ ∧
      ¬ FunctionallyEquivalent Γ₀ Γ₂ ∧
      ¬ FunctionallyEquivalent Γ₁ Γ₂ ∧
      (∀ (W' : Set U) (g : Bool), RefinesOn W' Γ₀ →
        ¬ PhysicallyKnows C₁ Γ₀ g W') ∧
      (∀ (W' : Set U) (g : Bool), RefinesOn W' Γ₁ →
        ¬ PhysicallyKnows C₁ Γ₁ g W') ∧
      (∀ (W' : Set U) (g : Bool), RefinesOn W' Γ₂ →
        ¬ PhysicallyKnows C₁ Γ₂ g W') := by
  obtain ⟨K⟩ := hknow
  obtain ⟨Γ₀, Γ₁, Γ₂, hsurj₀, hsurj₁, hsurj₂,
      hneq₀₁, hneq₀₂, hneq₁₂, hnot₀, hnot₁, hnot₂⟩ :=
    exists_three_inequivalent_not_weaklyInfers hdist hneq K.weaklyInfers
  refine ⟨Γ₀, Γ₁, Γ₂, hsurj₀, hsurj₁, hsurj₂,
    hneq₀₁, hneq₀₂, hneq₁₂, ?_, ?_, ?_⟩
  · intro W' g _ h
    exact hnot₀ h.weaklyInfers
  · intro W' g _ h
    exact hnot₁ h.weaklyInfers
  · intro W' g _ h
    exact hnot₂ h.weaklyInfers

end AISafetyAtlas.Inference
