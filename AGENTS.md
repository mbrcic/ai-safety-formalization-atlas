# Contributor and Agent Guidance

## Public Lean API

Treat `AISafetyAtlas` as a small, stable facade over proofs that may live in
Mathlib, this repository, or another maintained Lean package. Downstream users
and agents should not need to know the location of an upstream declaration.

- Expose one canonical public declaration for each mathematical result.
- Preserve the theorem's conventional, recognizable name whenever one exists.
- Use the form `AISafetyAtlas.<Domain>.<OptionalRepresentation>.<Theorem>`.
- Use `UpperCamelCase` for namespaces and Lean's `snake_case` for declarations.
- Introduce a representation namespace only when it supplies a meaningfully
  different interface needed by downstream proofs.
- Add a suffix such as `_iff`, `_reduction`, or `_undecidable` only when it
  identifies a genuinely useful distinction.
- Do not turn theorem names into namespaces merely to group variants.
- Do not mirror all upstream declarations. Add only the stable aliases that
  make the atlas easier to use.

Preferred examples include:

```lean
AISafetyAtlas.Computability.rice
AISafetyAtlas.SocialChoice.arrow
AISafetyAtlas.SocialChoice.Utility.arrow
AISafetyAtlas.Logic.godel_first_incompleteness
AISafetyAtlas.Logic.godel_second_incompleteness
AISafetyAtlas.Logic.tarski_undefinability
AISafetyAtlas.Logic.loeb
AISafetyAtlas.Learning.no_free_lunch
```

## Parsimony and Multiple Formalizations

Minimize semantic and API redundancy. Reuse a maintained Lean result and place
a stable atlas alias or a thin interface bridge over it before porting another
proof of the same theorem.

Keep an additional formalization only when it provides a documented,
substantial gain, such as:

- a stronger theorem needed by intended proofs;
- a materially different representation, such as a utility-facing interface;
- an explicit reduction certificate needed for compositional arguments;
- constructive or computational content that the canonical result lacks; or
- necessary independence from an unsuitable upstream dependency.

Alternative Coq, Rocq, Isabelle, or other proofs may be recorded as provenance
without becoming duplicate public Lean declarations or separate coverage
claims. Explain the unique value before adding a second public formalization.

For Arrow's theorem, prefer one canonical Lean proof and derive a utility-facing
bridge from it when possible. For Rice's theorem, do not duplicate the ordinary
undecidability result; add an explicit one-reduction or a c.e.-set interface only
when downstream work actually requires that extra structure.

These rules are defaults. Override them only when the significant gain is
recorded in the relevant source, registry entry, or design documentation.
