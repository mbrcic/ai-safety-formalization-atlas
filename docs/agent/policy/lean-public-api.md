## Public Lean API

**`AISafetyAtlas/Examples/` is not API and is not pinned.** A worked witness
exists to show a theorem is not vacuous; it is not something downstream should
build on, and committing to its name would make renaming an example a breaking
change. Until 2026-09-16 the pin included them, and they were 1,049 of 3,262
entries — 485 added by one witness campaign — so a third of the "stable facade"
was one-off instances. Examples are still built, still covered by the axiom
audit, and still what `check_witness_debt` reads; they are simply not promises.
`check_public_api.py` skips them, and dropping them does not move the
witness-debt denominator, which already excluded them.

`AISafetyAtlas` is a small stable facade. One canonical public declaration per
result; keep conventional theorem names; namespace form
`AISafetyAtlas.<Domain>.<OptionalRepresentation>.<Theorem>` (`UpperCamelCase`
namespaces, `snake_case` declarations). Add representation namespaces or
suffixes (`_iff`, `_reduction`, …) only for genuine interface distinctions.
Do not mirror entire upstream libraries.

```lean
AISafetyAtlas.Computability.rice
AISafetyAtlas.Verification.rice
AISafetyAtlas.Verification.AgentBehavior.no_behavioral_safety_verifier
AISafetyAtlas.Verification.Robot.action_safety_unverifiable
AISafetyAtlas.SocialChoice.arrow
AISafetyAtlas.SocialChoice.Utility.arrow
AISafetyAtlas.SocialChoice.gibbard_satterthwaite
AISafetyAtlas.Logic.godel_first_incompleteness
AISafetyAtlas.Logic.godel_second_incompleteness
AISafetyAtlas.Logic.tarski_undefinability
AISafetyAtlas.Logic.loeb
AISafetyAtlas.Explainability.attribution_impossibility
AISafetyAtlas.Learning.no_free_lunch
AISafetyAtlas.SelfAwareness.Model.limited_self_awareness
```
