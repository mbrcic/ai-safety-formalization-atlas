module

public import AISafetyAtlas.Preference.SourceComplexity

/-!
# Propositions 7 and 8, source parameterization, at the constant-zero language

`ReasonableForF` needs no work to instantiate: the all-zero complexity
assignment is trivially `0`-reasonable for `F`, since every inequality reduces
to `0 ≤ 0`. This is enough to exercise the compatibility lemmas, which do not
depend on the constant being nontrivial.
-/

namespace AISafetyAtlas.Examples.Preference

open AISafetyAtlas.Preference.Source

/-- The constant-zero complexity assignment: `0`-reasonable for `F`, trivially. -/
public def zeroLanguage : ReasonableForF Bool Bool where
  KPair := fun _ => 0
  c := 0
  F_complexity_le := fun _ _ => le_refl 0

/-- `Compatible` and `ReasonableLanguage.Compatible` agree, at a concrete
policy and its indifferent pair. -/
theorem zeroLanguage_compatible_iff (π : AISafetyAtlas.Preference.Policy Bool Bool) :
    ReasonableForF.Compatible (S := Bool) (A := Bool)
        (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π)) π ↔
      AISafetyAtlas.Preference.ReasonableLanguage.Compatible
        (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π)) π :=
  ReasonableForF.compatible_iff _ π

/-- Negating `AmongLowestCompatible` is `NotAmongLowestCompatible`, at the
indifferent pair for a concrete policy. -/
theorem zeroLanguage_notAmongLowest_iff (π : AISafetyAtlas.Preference.Policy Bool Bool) :
    zeroLanguage.NotAmongLowestCompatible π
        (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π)) ↔
      ¬ zeroLanguage.AmongLowestCompatible π
        (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π)) :=
  ReasonableForF.notAmongLowest_iff zeroLanguage π _
    (ReasonableForF.compatible_indifferent π)

/-! ## Armstrong and Mindermann's three propositions, at the zero language

`zeroLanguage` inhabits `ReasonableForF` with no work at all, which is the point
of the abstraction. What it was not used for is running the three numbered
results that quantify over every such language.
-/

/-- **Proposition 7.** The three degenerate planner-reward pairs are all among
the lowest-complexity explanations of any policy — which is the statement that
makes the degeneracy a problem rather than a curiosity. -/
public theorem zero_proposition_seven (π : AISafetyAtlas.Preference.Policy Bool Bool) :
    zeroLanguage.AmongLowestCompatible π
        (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π)) ∧
      zeroLanguage.AmongLowestCompatible π
        (AISafetyAtlas.Preference.op2 (AISafetyAtlas.Preference.op6 π)) ∧
      zeroLanguage.AmongLowestCompatible π
        (AISafetyAtlas.Preference.op4
          (AISafetyAtlas.Preference.op2 (AISafetyAtlas.Preference.op6 π))) :=
  ReasonableForF.proposition_seven zeroLanguage π

/-- **Proposition 8.** Negating the reward preserves compatibility and moves the
complexity by at most the language's constant, in both directions. So the
anti-rational pair is no harder to write down than the intended one. -/
public theorem zero_proposition_eight {x : AISafetyAtlas.Preference.Pair Bool Bool}
    {π : AISafetyAtlas.Preference.Policy Bool Bool}
    (h : AISafetyAtlas.Preference.Source.ReasonableForF.Compatible x π) :
    AISafetyAtlas.Preference.Source.ReasonableForF.Compatible (AISafetyAtlas.Preference.Source.F₄ x) π ∧
      zeroLanguage.KPair (AISafetyAtlas.Preference.Source.F₄ x) ≤ zeroLanguage.KPair x + zeroLanguage.c ∧
      zeroLanguage.KPair x ≤ zeroLanguage.KPair (AISafetyAtlas.Preference.Source.F₄ x) + zeroLanguage.c :=
  ReasonableForF.proposition_eight zeroLanguage h

/-- **Theorem 2, conditionally.** If the intended pair is *not* among the lowest,
all three degenerate pairs are strictly simpler than it — so complexity does not
single out the intended explanation, it actively prefers the degenerate ones. -/
public theorem zero_theorem_two (π : AISafetyAtlas.Preference.Policy Bool Bool)
    (intended : AISafetyAtlas.Preference.Pair Bool Bool)
    (h9 : zeroLanguage.NotAmongLowestCompatible π intended) :
    zeroLanguage.KPair (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π))
        < zeroLanguage.KPair intended ∧
      zeroLanguage.KPair (AISafetyAtlas.Preference.op2 (AISafetyAtlas.Preference.op6 π))
        < zeroLanguage.KPair intended ∧
      zeroLanguage.KPair (AISafetyAtlas.Preference.op4
          (AISafetyAtlas.Preference.op2 (AISafetyAtlas.Preference.op6 π)))
        < zeroLanguage.KPair intended :=
  ReasonableForF.theorem_two_conditional zeroLanguage π intended h9

end AISafetyAtlas.Examples.Preference
