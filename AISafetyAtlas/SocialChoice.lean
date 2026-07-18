module

public import AISafetyAtlas.Upstream.Arrow

/-!
# Social choice

A stable atlas facade over a pinned, vendored snapshot of CC Liang's Lean 4
formalization of Arrow's impossibility theorem. These names isolate downstream
work from the upstream declaration layout.
-/

namespace AISafetyAtlas.SocialChoice

/-- A complete and transitive weak preference relation, allowing ties. -/
public abbrev Preference := AISafetyAtlas.Upstream.Arrow.Preorder'

/-- A profile of `voterCount` preferences over `Alternative`. -/
public abbrev Profile (Alternative : Type) (voterCount : ℕ) :=
  AISafetyAtlas.Upstream.Arrow.Profile Alternative voterCount

/-- A rule that aggregates a preference profile into a social preference. -/
public abbrev SocialWelfareFunction (Alternative : Type) (voterCount : ℕ) :=
  AISafetyAtlas.Upstream.Arrow.SWF Alternative voterCount

/-- The Pareto/unanimity condition for a social welfare function. -/
public abbrev Unanimity {Alternative : Type} {voterCount : ℕ}
    (rule : SocialWelfareFunction Alternative voterCount) : Prop :=
  AISafetyAtlas.Upstream.Arrow.Unanimity rule

/-- Independence of irrelevant alternatives. -/
public abbrev IndependenceOfIrrelevantAlternatives
    {Alternative : Type} {voterCount : ℕ}
    (rule : SocialWelfareFunction Alternative voterCount) : Prop :=
  AISafetyAtlas.Upstream.Arrow.IIA rule

/-- No voter dictates every pairwise social preference. -/
public abbrev NonDictatorship {Alternative : Type} {voterCount : ℕ}
    (rule : SocialWelfareFunction Alternative voterCount) : Prop :=
  AISafetyAtlas.Upstream.Arrow.NonDictatorship rule

/--
Arrow's impossibility theorem: with at least one voter and at least three
alternatives, no social welfare function satisfies unanimity, independence of
irrelevant alternatives, and non-dictatorship simultaneously.

Source: `Impossibility` in CC Liang's `arrow` repository, vendored from commit
`758398779decc66d2830a70b02597b0f22030181`.
-/
public theorem arrow
    {Alternative : Type} {voterCount : ℕ}
    [NeZero voterCount] [Fintype Alternative]
    (atLeastThree : Fintype.card Alternative ≥ 3) :
    ¬ ∃ rule : SocialWelfareFunction Alternative voterCount,
      Unanimity rule ∧
      IndependenceOfIrrelevantAlternatives rule ∧
      NonDictatorship rule :=
  AISafetyAtlas.Upstream.Arrow.Impossibility atLeastThree

end AISafetyAtlas.SocialChoice
