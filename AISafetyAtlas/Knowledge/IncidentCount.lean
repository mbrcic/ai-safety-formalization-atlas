module

public import AISafetyAtlas.Knowledge

/-!
# When is it one incident or two, and what that does to a count

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four layers:
*(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Knowledge`, which is about
observations and decoders and names no incident. What is added here is the
reading as an **incident reporting regime**, and one consequence that is about
numbers rather than about knowledge.

## The question

Sidhu et al., *Open Problems in AI Incident Governance* (arXiv, 2026), ask when a
single AI incident begins and ends, and when harm traced to one model counts as
one incident or many. That is an **individuation** question: not what happened,
but how many things happened.

It looks like a definitional problem to be settled by agreeing a taxonomy. The
statement below says what such an agreement has to achieve, and where agreement
alone cannot reach.

## What is stated

`Reporting` is a regime: what a deployment actually files, and how many incidents
actually occurred.

`count_not_determined_of_collision` is the obstruction in the familiar shape —
two deployments that file identically and differ in their incident count admit no
decoder, so no counting rule over filings recovers the number.

`count_is_not_a_measurement` is the part worth having, and it is about numbers.
Under such a collision, **the count a regime publishes is a function of its
filing schema and not of the incidents**. Two deployments can be identical in
everything the regime records and differ in what actually happened. Published
counts can still be compared with each other and with targets; what the
comparison does not show is a fact about incidents. A count that meets a target
expressed in incidents does not show the incidents meet it, and a difference
across regimes, or across a schema change, may reflect the schemas.

`schema_fixes_the_count` is the positive half, and it is only the definition
unfolded: where the filing does determine the count, a counting rule exists. Under
a collision no counting rule is the repair, because the obstruction quantifies
over every rule. A richer form could be, but only if what it records determines
the true count, which presupposes an answer to what counts as one incident and
that filings are complete and honest. Nothing here says such a form exists.

## What this does not claim

The atlas has **no incident, no taxonomy and no reporting standard.** Nothing here
says any real regime collides, and exhibiting the two deployments is an empirical
claim about a schema that this repository does not make.

Nor is this an argument against counting incidents. It is an argument that a
count inherits the resolution of the schema it is computed from, which is a
reason to specify the schema first and not a reason to stop counting.

Identifying `report` with any real filing, or `count` with any published figure,
is layer 4 and is not done here.
-/

namespace AISafetyAtlas.Knowledge.IncidentCount

universe u v

variable {Ω : Type u} {R : Type v}

/--
An **incident reporting regime**: what a deployment files, and how many incidents
actually occurred there.

Nothing constrains `report` to be honest or complete, and nothing relates it to
`count`. The theorems take whatever relationship they need as a hypothesis.
-/
public structure Reporting (Ω : Type u) (R : Type v) where
  /-- Everything the regime records about a deployment. -/
  report : Ω → R
  /-- How many incidents actually occurred. -/
  count : Ω → Nat

variable (G : Reporting Ω R)

/-- **The obstruction.** Two deployments that file identically and differ in their
incident count admit no counting rule over filings. -/
public theorem count_not_determined_of_collision {ω ω' : Ω}
    (hsame : G.report ω = G.report ω') (hdiff : G.count ω ≠ G.count ω') :
    ¬ Knowable G.report G.count :=
  not_knowable_of_collision hsame hdiff

/--
**The published count is a property of the schema, not of the incidents.**

Given such a pair, for **every** counting rule there are two deployments the rule
scores identically whose true counts differ. So the number a regime publishes
does not determine the true count: meeting a target expressed in incidents does
not show the incidents meet it, and a difference from a regime that files
differently, or from before a schema change, may reflect the schemas.

The quantifier over rules is what the statement adds: it is not about the
counting methodologies anyone has proposed. The proof is the hypotheses
restated (`congrArg` on `hsame`, and `hdiff`); the content is in reading them
for every rule at once. `count` assumes the individuation question already has
an answer: it says how many incidents there were.
-/
public theorem count_is_not_a_measurement {ω ω' : Ω}
    (hsame : G.report ω = G.report ω') (hdiff : G.count ω ≠ G.count ω') :
    ∀ rule : R → Nat, rule (G.report ω) = rule (G.report ω') ∧ G.count ω ≠ G.count ω' :=
  fun rule => ⟨congrArg rule hsame, hdiff⟩

/--
**Where the filing determines the count, a counting rule exists.** This is
`Knowable` unfolded and proves nothing beyond the definition; it does not say any
real form determines the count.

Stated so that the two sit together: the obstruction quantifies over every rule,
so no rule is the repair, and this says what a repair would have to achieve.
-/
public theorem schema_fixes_the_count (h : Knowable G.report G.count) :
    ∃ rule : R → Nat, ∀ ω, G.count ω = rule (G.report ω) := h

/--
**And a regime that files the count itself has no obstruction**, which keeps the
positive half from being a hypothesis nothing satisfies.
-/
public theorem knowable_of_report_carries_count
    (hcarries : ∀ ω ω', G.report ω = G.report ω' → G.count ω = G.count ω') :
    Knowable G.report G.count :=
  (knowable_iff_no_collision G.report G.count).mpr hcarries

end AISafetyAtlas.Knowledge.IncidentCount
