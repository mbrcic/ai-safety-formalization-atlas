module

public import AISafetyAtlas.SocialChoice
public import Mathlib.Data.Real.Basic

/-!
# Utility-facing Arrow theorem

## Statement intent

- Objects: real-valued utilities over a finite alternative type and profiles
  indexed by `Fin voterCount`.
- Assumptions: at least one voter, at least three alternatives, unanimity, and
  pairwise independence of irrelevant alternatives.
- Conclusion: no utility-valued social welfare function is simultaneously
  non-dictatorial.
- Bridge: every total preorder on a finite type is represented by the cardinality
  of its lower contour set. This converts a utility aggregator into the order
  aggregator used by `AISafetyAtlas.SocialChoice.arrow`.
- Difference from Isabelle: this theorem reuses the canonical Lean order proof;
  it does not port Isabelle's independent utility-based proof.
-/

namespace AISafetyAtlas.SocialChoice.Utility

open Classical

noncomputable section

/-- A real-valued utility function over alternatives. -/
public abbrev Function (Alternative : Type) := Alternative → ℝ

/-- A profile of utility functions, one for each voter. -/
public abbrev Profile (Alternative : Type) (voterCount : ℕ) :=
  Fin voterCount → Function Alternative

/-- A rule that aggregates a utility profile into a social utility function. -/
public abbrev SocialWelfareFunction (Alternative : Type) (voterCount : ℕ) :=
  Profile Alternative voterCount → Function Alternative

/-- The weak preference induced by a utility function. -/
public def preference {Alternative : Type} (utility : Function Alternative) :
    AISafetyAtlas.SocialChoice.Preference Alternative where
  le a b := utility a ≤ utility b
  refl _ := le_rfl
  trans _ _ _ := le_trans
  total _ _ := le_total _ _

@[simp]
public theorem preference_le_iff {Alternative : Type}
    (utility : Function Alternative) (a b : Alternative) :
    (preference utility).le a b ↔ utility a ≤ utility b :=
  Iff.rfl

/-- Unanimity/Pareto expressed through strict utility comparison. -/
public def Unanimity {Alternative : Type} {voterCount : ℕ}
    (rule : SocialWelfareFunction Alternative voterCount) : Prop :=
  ∀ profile a b,
    (∀ voter, profile voter b < profile voter a) →
    rule profile b < rule profile a

/-- Each social pairwise comparison depends only on individual comparisons. -/
public def IndependenceOfIrrelevantAlternatives
    {Alternative : Type} {voterCount : ℕ}
    (rule : SocialWelfareFunction Alternative voterCount) : Prop :=
  ∀ profile₁ profile₂ a b,
    (∀ voter, profile₁ voter a ≤ profile₁ voter b ↔
      profile₂ voter a ≤ profile₂ voter b) →
    (rule profile₁ a ≤ rule profile₁ b ↔
      rule profile₂ a ≤ rule profile₂ b)

/-- No voter can force every strict pairwise social comparison. -/
public def NonDictatorship {Alternative : Type} {voterCount : ℕ}
    (rule : SocialWelfareFunction Alternative voterCount) : Prop :=
  ¬ ∃ dictator : Fin voterCount, ∀ profile a b,
    a ≠ b → profile dictator b < profile dictator a →
    rule profile b < rule profile a

/-- Alternatives weakly below `a` in a preference relation. -/
private def lowerContour {Alternative : Type} [Fintype Alternative]
    (pref : AISafetyAtlas.SocialChoice.Preference Alternative)
    (a : Alternative) : Finset Alternative :=
  Finset.univ.filter fun x => pref.le x a

/-- A real-valued representation of a finite total preorder. -/
private def representation {Alternative : Type} [Fintype Alternative]
    (pref : AISafetyAtlas.SocialChoice.Preference Alternative) :
    Function Alternative :=
  fun a => (lowerContour pref a).card

private theorem lowerContour_mono {Alternative : Type} [Fintype Alternative]
    {pref : AISafetyAtlas.SocialChoice.Preference Alternative}
    {a b : Alternative} (hab : pref.le a b) :
    lowerContour pref a ⊆ lowerContour pref b := by
  intro x hx
  simp only [lowerContour, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact pref.trans x a b hx hab

private theorem representation_le_iff
    {Alternative : Type} [Fintype Alternative]
    (pref : AISafetyAtlas.SocialChoice.Preference Alternative)
    (a b : Alternative) :
    representation pref a ≤ representation pref b ↔ pref.le a b := by
  constructor
  · intro hcard
    by_contra hab
    have hba : pref.le b a := (pref.total a b).resolve_left hab
    have hsubset : lowerContour pref b ⊆ lowerContour pref a :=
      lowerContour_mono hba
    have ha : a ∈ lowerContour pref a := by
      simp [lowerContour, pref.refl]
    have hna : a ∉ lowerContour pref b := by
      simp [lowerContour, hab]
    have hproper : lowerContour pref b ⊂ lowerContour pref a :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, by
        intro heq
        exact hna (heq ▸ ha)⟩
    have hlt : (lowerContour pref b).card < (lowerContour pref a).card :=
      Finset.card_lt_card hproper
    apply (not_lt_of_ge hcard)
    change ((lowerContour pref b).card : ℝ) <
      (lowerContour pref a).card
    exact_mod_cast hlt
  · intro hab
    have hcard := Finset.card_le_card (lowerContour_mono hab)
    change ((lowerContour pref a).card : ℝ) ≤
      (lowerContour pref b).card
    exact_mod_cast hcard

@[simp]
private theorem representation_preference_le_iff
    {Alternative : Type} [Fintype Alternative]
    (utility : Function Alternative) (a b : Alternative) :
    representation (preference utility) a ≤
      representation (preference utility) b ↔ utility a ≤ utility b := by
  rw [representation_le_iff]
  rfl

/-- Convert a utility aggregator into the canonical order-based model. -/
private def orderRule {Alternative : Type} {voterCount : ℕ}
    [Fintype Alternative]
    (rule : SocialWelfareFunction Alternative voterCount) :
    AISafetyAtlas.SocialChoice.SocialWelfareFunction Alternative voterCount :=
  fun profile =>
    preference (rule fun voter => representation (profile voter))

private theorem orderRule_unanimity
    {Alternative : Type} {voterCount : ℕ}
    [NeZero voterCount] [Fintype Alternative]
    {rule : SocialWelfareFunction Alternative voterCount}
    (hunanimity : Unanimity rule) :
    AISafetyAtlas.SocialChoice.Unanimity (orderRule rule) := by
  unfold AISafetyAtlas.SocialChoice.Unanimity
  rw [AISafetyAtlas.Upstream.Arrow.unanimity_iff]
  intro profile a b hpref
  have hutilities : ∀ voter,
      representation (profile voter) b < representation (profile voter) a := by
    intro voter
    have hp := AISafetyAtlas.Upstream.Arrow.Preorder'.lt_iff
      (profile voter) b a |>.mp (hpref voter)
    exact lt_of_not_ge
      (fun h => hp.2 ((representation_le_iff _ _ _).1 h))
  have hout := hunanimity _ a b hutilities
  apply (AISafetyAtlas.Upstream.Arrow.Preorder'.lt_iff _ _ _).2
  exact ⟨le_of_lt hout, not_le_of_gt hout⟩

private theorem orderRule_iia
    {Alternative : Type} {voterCount : ℕ}
    [NeZero voterCount] [Fintype Alternative]
    {rule : SocialWelfareFunction Alternative voterCount}
    (hiia : IndependenceOfIrrelevantAlternatives rule) :
    AISafetyAtlas.SocialChoice.IndependenceOfIrrelevantAlternatives
      (orderRule rule) := by
  unfold AISafetyAtlas.SocialChoice.IndependenceOfIrrelevantAlternatives
  rw [AISafetyAtlas.Upstream.Arrow.iia_iff]
  intro profile₁ profile₂ a b hagree
  constructor
  · simpa [orderRule, preference] using
      hiia _ _ b a (fun voter => by
        rw [representation_le_iff, representation_le_iff]
        exact (hagree voter).1)
  · simpa [orderRule, preference] using
      hiia _ _ a b (fun voter => by
        rw [representation_le_iff, representation_le_iff]
        exact (hagree voter).2)

private theorem orderRule_nonDictatorship
    {Alternative : Type} {voterCount : ℕ}
    [NeZero voterCount] [Fintype Alternative]
    {rule : SocialWelfareFunction Alternative voterCount}
    (hiia : IndependenceOfIrrelevantAlternatives rule)
    (hnondictator : NonDictatorship rule) :
    AISafetyAtlas.SocialChoice.NonDictatorship (orderRule rule) := by
  unfold AISafetyAtlas.SocialChoice.NonDictatorship
  rw [AISafetyAtlas.Upstream.Arrow.nonDictatorship_iff]
  intro hdictator
  apply hnondictator
  obtain ⟨dictator, hdictator⟩ := hdictator
  refine ⟨dictator, ?_⟩
  intro profile a b hab hpref
  let orderProfile : AISafetyAtlas.SocialChoice.Profile Alternative voterCount :=
    fun voter => preference (profile voter)
  let representedProfile : Profile Alternative voterCount :=
    fun voter => representation (orderProfile voter)
  have horderPreference :
      AISafetyAtlas.Upstream.Arrow.Preorder'.lt
        (orderProfile dictator) b a := by
    apply (AISafetyAtlas.Upstream.Arrow.Preorder'.lt_iff _ _ _).2
    exact ⟨le_of_lt hpref, not_le_of_gt hpref⟩
  have hrepresented :
      rule representedProfile b < rule representedProfile a := by
    have := hdictator a b hab orderProfile horderPreference
    have hpair :=
      (AISafetyAtlas.Upstream.Arrow.Preorder'.lt_iff _ _ _).1 this
    exact lt_of_not_ge hpair.2
  apply lt_of_not_ge
  intro hreverse
  ·
    apply (not_le_of_gt hrepresented)
    exact (hiia representedProfile profile a b (fun voter => by
      exact representation_preference_le_iff (profile voter) a b)).mpr
      hreverse

/--
Arrow's impossibility theorem for real-valued utility aggregation.

This is a representation bridge to `AISafetyAtlas.SocialChoice.arrow`, not an
independent second proof of Arrow's mathematical core.
-/
public theorem arrow
    {Alternative : Type} {voterCount : ℕ}
    [NeZero voterCount] [Fintype Alternative]
    (atLeastThree : Fintype.card Alternative ≥ 3) :
    ¬ ∃ rule : SocialWelfareFunction Alternative voterCount,
      Unanimity rule ∧
      IndependenceOfIrrelevantAlternatives rule ∧
      NonDictatorship rule := by
  rintro ⟨rule, hunanimity, hiia, hnondictator⟩
  exact AISafetyAtlas.SocialChoice.arrow atLeastThree
    ⟨orderRule rule, orderRule_unanimity hunanimity,
      orderRule_iia hiia, orderRule_nonDictatorship hiia hnondictator⟩

end

end AISafetyAtlas.SocialChoice.Utility
