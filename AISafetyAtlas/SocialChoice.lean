module

public import AISafetyAtlas.Upstream.Arrow
public import AISafetyAtlas.Upstream.GibbardSatterthwaite

/-!
# Social choice

Stable atlas facades over pinned, vendored social-choice formalizations:

* **Arrow** — CC Liang's Lean 4 weak-order social welfare function proof
  (`AISafetyAtlas.Upstream.Arrow`).
* **Gibbard–Satterthwaite** — classical resolute voting-rule form from
  SocialChoiceLean (Dominik Peters et al.), vendored as
  `AISafetyAtlas/Upstream/GibbardSatterthwaite.lean` (MIT, pin `74f491b`;
  multi-file upstream layout collapsed to one module for the atlas boundary).

The two results use different ballot models (weak orders vs linear orders) and
different rule shapes (SWF vs resolute choice). Facade names isolate downstream
work from upstream declaration layout.
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

/-! ## Gibbard–Satterthwaite (resolute voting rules)

Linear-order ballots and resolute voting rules
(`_root_.SocialChoice.VotingRule`). These abbreviations re-export the vendored
SocialChoiceLean interface so downstream proofs need not import the Upstream
path. Qualified via `_root_` because this namespace is also named `SocialChoice`.
-/

/-- Finite electorate × candidate linear-order profile (SocialChoiceLean). -/
public abbrev VotingProfile (V A : Type) [Fintype V] [Fintype A] :=
  _root_.SocialChoice.Profile V A

/-- Polymorphic resolute-capable voting rule on finite electorates. -/
public abbrev VotingRule := _root_.SocialChoice.VotingRule

/-- Unique-winner (resolute) voting rules. -/
public abbrev ResoluteVoting := _root_.SocialChoice.Resolute

/-- Unanimity for resolute voting rules (SocialChoiceLean form). -/
public abbrev VotingUnanimity := _root_.SocialChoice.Unanimity

/-- Strategy-proofness for resolute voting rules. -/
public abbrev ResoluteStrategyproofness :=
  _root_.SocialChoice.ResoluteStrategyproofness

/-- Top-ranked candidate under a linear-order ballot (SocialChoiceLean). -/
public noncomputable abbrev topChoice {V A : Type}
    [Fintype V] [Fintype A] [Nonempty A]
    (P : VotingProfile V A) (v : V) : A :=
  _root_.SocialChoice.topChoice P v

/--
Gibbard–Satterthwaite: with at least three candidates, every resolute,
unanimous, strategy-proof voting rule is dictatorial (some voter's top choice
is always the unique winner).

Source: `_root_.SocialChoice.gibbard_satterthwaite` in SocialChoiceLean,
vendored from `mbrcic/SocialChoiceLean` revision `74f491b` (`port/lean-4.31`),
file `AISafetyAtlas/Upstream/GibbardSatterthwaite.lean`.
-/
public theorem gibbard_satterthwaite
    {V A : Type} [Fintype V] [Nonempty V] [Fintype A] [Nonempty A]
    (hcardA : 3 ≤ Fintype.card A)
    (f : VotingRule)
    (hf_res : ResoluteVoting f)
    (hf_unan : VotingUnanimity f)
    (hf_sp : ResoluteStrategyproofness f hf_res) :
    ∃ d : V, ∀ P : VotingProfile V A, f P = {topChoice P d} :=
  _root_.SocialChoice.gibbard_satterthwaite hcardA f hf_res hf_unan hf_sp

end AISafetyAtlas.SocialChoice
