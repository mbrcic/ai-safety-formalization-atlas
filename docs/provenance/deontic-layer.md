# The deontic layer — what was taken, and what was decided

**Date.** 2026-09-13. Row `LAND-SOV-DEONTIC-001`.

This note exists because the module is **mostly a design decision and only
partly a transcription**, and the two must not be confused by a later reader.

## What came from print

One sentence, from one source; a second source was read and **diverges**, which
is recorded below rather than folded in.

Jones & Sergot, *A Formal Characterisation of Institutionalised
Power*, J. of the IGPL **4**(3):427–443, 1996 — held, sha256 `e5ebe993…`,
manifested in the private manifest of 2026-09-12. **Abstract, p. 427,
read 2026-09-13 from a rendered page image:**

> Following a lead from jurisprudential discussions of *legal power*, we
> distinguish *institutionalised power* from *permission* and *practical
> possibility*.

`InstitutionalSetting` carries those three as separate fields, and `Separated`
is the formal content of "distinguish": **every combination of the three is
realized**. That is the strongest available reading — a weaker one ("the three
are not the same predicate") would be satisfied by three predicates differing on
a single act — and `Examples.Sovereignty.Deontic.cube_separated` discharges it by
`decide` over eight acts, one per combination.

**A correction to this repository's own earlier note.** the private manifest of 2026-09-12
recorded that the year on the running foot was OCR rubble and that 1996 was
inferred. Re-rendered at 155 dpi, the foot reads *"J. of the IGPL, Vol. 4 No. 3,
pp. 427-443 1996"* — the year **is** on the face. The earlier note was a
rendering artefact, not a property of the document.

### A second source, read and diverging — Ågotnes, van der Hoek & Wooldridge 2007

*Normative System Games*, AAMAS'07, pp. 881–888. Held, sha256 `edad8e31…`,
manifested in the same file. **Read 2026-09-13, all eight pages, from rendered
page images**, because an outside package named it as the anchor for exactly this
module's four sub-concepts. It anchors one of them.

Their normative system, §3, p. 883, is **one** set: `η ⊆ R`, the forbidden
transitions, with the permitted ones — their word is *legal* — the complement
`R \ η`. So their object is consistent and complete **by construction**, which is
the corner `NormSystem.forbidden_iff_not_permitted_iff` isolates. This is not
evidence against the two-annotation design; it is the two-valued special case of
it, and the theorem says precisely where it sits.

Neither *obligation* nor *ought* occurs anywhere in their body — a full-text scan
of all eight pages returns one line containing any of *obligation*, *ought*,
*permitted* or *deontic*, and it is a bibliography entry. Their agents carry CTL
goal hierarchies and ordinal utility, and compliance is a game-theoretic choice,
not a deontic status. So `OughtImpliesCan` here has **no anchor** and is not
claimed to have one; the pointer their own bibliography gives is Wooldridge & van
der Hoek, *On obligations and normative ability: Towards a logical analysis of the
social contract*, J. Applied Logic **3**:396–420, 2005,
doi `10.1016/j.jal.2005.04.006`.

**That paper is held since 2026-09-13**, sha256 `21970069…`, manifested in
the private manifest of 2026-09-13. **Body read the same day**
and graded in section 27 of `source-coverage-audit.md` — 0 Yes, 5 Partial, 22 No,
1 Beyond. It **defines** obligation rather than taking it as primitive. Journal
page 408, from a rendered page image:

> `P_η φ ≜ ⟪η : Ag⟫φ`   `O_η φ ≜ ¬P_η ¬φ`

> *φ is said to be permissible within the context of normative system η iff the
> grand coalition of agents can cooperate to achieve φ within the context of η*
> … *φ is said to be obligatory within the context of normative system η iff φ is
> inevitable if the grand coalition conforms to η.*

So `OughtImpliesCan`'s decision to carry obligation as an **arbitrary parameter**
now has a named published alternative. Three things follow, and the third
corrects what this note said before the body was read.

**One. Their definition makes obligation imply permission.** Journal page 410,
for non-trivial `η`: `⊨ (Aφ → O_η φ)`, `⊨ (O_η φ → P_η φ)`, `⊨ (P_η φ → Eφ)`.
The middle link fails *only* at `η⊤`, where — print's own words — `O_η φ` holds
for every `φ` while `P_η ψ` holds for no `ψ`: vacuity, not separation. So
`oughtImpliesCan_does_not_give_permission` is **not** an instance of anything
here. That theorem exists because obligation is a free parameter, and print's
definition is exactly a case where its conclusion is false. The two results are
about different objects and neither supports the other.

**Two. Their obligation does not imply guaranteed ability**, same page:
`⊭ O_η φ → ⟪η : C⟫φ` and `⊭ O_η φ → ⟪C⟫φ`, because *"the fact that something is
obligatory does not imply that any individual coalition can achieve it"*. This
is **not** a refutation of ought-implies-can. `⊨ O_η φ → P_η φ → Eφ` on the same
page gives *some way exists*, which is the shape `InstitutionalSetting.possible`
has; what fails is the stronger *some coalition can guarantee it*, which the
atlas's `possible` is not.

**Three, and this corrects this note.** An earlier revision said that adopting
their definition "is adopting their normative ATL". **That is false**, and the
grading is what showed it. `P_η` and `O_η` need three things: a restriction of
which strategies are conformant, coalition forcing, and a negation. The
`Sovereignty` cluster has all three — `Forces`, `Enlarges` (which is the
conformant-strategy inclusion in the abstract), and set complement. What needs
ATL is the *temporal* object print then argues is the interesting one, since by
its equation (2) on page 409 the deontic status of a non-temporal formula is
trivial: `⊨ (σ ↔ P_η σ) ∧ (σ ↔ O_η σ)` for objective `σ`.

So the outcome-set fragment of their deontic layer is **cheap and buildable
here**, and it is still not built, because building it is answering the question
"which deontic logic does the atlas adopt?" — which remains the maintainer's.
This note is the costing, not a plan.

### One condition of theirs the atlas deliberately refuses

Journal page 402 places a standing requirement on every normative system:

> `∀α ∈ Ac_Ag: (Q \ ρ(α)) ⊆ η(α)`

— *"they forbid anything that is forbidden by 'nature'"*, with `ρ` the
precondition function and `η(α)` the states where `α` is forbidden. Print
therefore **couples prohibition to possibility**: whatever cannot be done is
forbidden.

`InstitutionalSetting` keeps them apart, and `cube_separated` is the assertion
that they are apart — all eight combinations of empowered, permitted and possible
occur, including *impossible and permitted*. Under print's requirement that
combination cannot arise. This is a divergence, recorded here so that nobody
later reads the separation claim as compatible with their model; it is not an
omission, and it is the price of treating silence as distinct from prohibition.

**One condition of theirs that this module does not have.** *Reasonableness*:
`N(R) = {η : (η ⊆ R) & (R \ η is total)}`, which *"prevents normative systems
which lead to states with no successor"* — a **local, positive** requirement that
each state keep a permitted way out. `NormSystem E` cannot state it, having no
notion of which acts are available where; stating it needs one extra datum, a map
from acts to the state they leave from. That is a design decision and is left
open rather than guessed at. **It is recorded here so that nobody later mistakes
`Consistent` for it:** global consistency is neither local nor positive and is
not a substitute.

### What was deliberately not taken

The paper's conditional connective `⇒ₛ`, its minimal conditional model
`⟨W, f_s, P⟩` at p. 435, its action modality, and its explicit rejection of
`RCM` and `RI` (p. 433) and `PTR` (p. 435). None of that is here. This module
takes the separation claim and stops.

## What is an atlas-side decision

**`forbidden` is an independent positive predicate, not `¬ permitted`.** This is
not Jones & Sergot's and is not claimed to be.

| `permitted` | `forbidden` | status |
|---|---|---|
| yes | no | permitted |
| no | yes | forbidden |
| no | no | unclassified — the norms are silent |
| yes | yes | conflicted — the norms disagree |

The justification is `NormSystem.forbidden_iff_not_permitted_iff`: the four
statuses collapse to the classical two **exactly** at systems that are both
consistent and complete. So the two-valued reading is a special case rather than
a rival, nothing is given up, and what is bought is that *silence* and
*contradiction* become distinguishable objects. A single `permitted : E → Prop`
with `forbidden := ¬ permitted` makes every unregulated act forbidden, which is
the wrong default for a governance model and is not a position this repository
wants to take by accident.

`Examples.Sovereignty.Deontic.fourStatus` realizes all four statuses, and
`fourStatus_silence_is_not_prohibition` is the distinction at a witness.

**This is not a deontic logic.** No `O`, no `P` operator, no modal axiom, no
possible-worlds semantics, no inference relation. Obligation is left as a
*parameter* in `OughtImpliesCan` rather than defined from permission and
prohibition, because that identification is itself a deontic-logic commitment —
and, as the Wooldridge & van der Hoek reading above shows, a commitment with
consequences: at their definition obligation *does* imply permission wherever
anything is permitted.
The question "does the atlas take on a deontic logic?" is still open and this
module does not answer it; the question "does the atlas take on *may not*?" is
answered yes, at the smallest vocabulary that can say it.

## A third source, read and **anchoring** — Grossi, Gabbay & van der Torre 2010

*The Norm Implementation Problem in Normative Multi-Agent Systems*, ch. 7 of
Dastani, Hindriks & Meyer (eds.), *Specification and Verification of Multi-agent
Systems*, Springer 2010, folios 195–224. Held as the whole volume, sha256
`b076b12e…`, manifested in the private manifest of 2026-09-13 §6. **Read
2026-09-13 at folios 195, 212 and 216 from rendered page images.**

Unlike the previous two sources this one **anchors a construction**, not only a
sentence. Their subject is how a prohibition is *implemented*, and their two
answers differ on exactly one axis — the axis this module exists to keep apart.

| | Folio 212, §7.4.1 **Regimentation** | Folio 216, §7.5 **Perfect enforcement** |
|---|---|---|
| what moves | the transition relation: `R_a^{m′} := R_a^m − {(w,w′) \| (m,w) ⊨ pre_a & (m,w′) ⊨ viol(i)}` | the payoffs |
| what is fixed | payoffs | **the transitions**, and the printed conditions open by saying so: `W = W′`, `W_end = W′_end`, `{R_a} = {R′_a}` |
| in this module | `InstitutionalSetting.regiment` | `InstitutionalSetting.enforce` |
| the axis fact | `regiment_norms : (I.regiment bad).norms = I.norms`, `rfl` | `enforce_possible : (I.enforce bad).possible = I.possible`, `rfl` |

Their prose makes the point directly, folio 216: *"While regimentation makes it
impossible for the agents to reach a violation state, automatic enforcement
makes it just irrational in a decision-theoretic sense."*

### What this buys, beyond a citation

`regiment_unpermitted_not_separated`. Regiment against exactly the unpermitted
acts and `Separated` **fails** — possibility now entails permission, so there is
no act that is possible and not permitted and the three axes stop being
independent. `enforce_separated` transports `Separated` unchanged.

So the two are not two ways of saying the same thing. **Regimentation does not
record a prohibition; it removes the question the prohibition was asked about.**
That is stated here as a theorem rather than as a warning, and
`Examples.Sovereignty.Deontic.five_is_the_gap` fixes it at act `5` of `cube` —
empowered, possible, unpermitted — which regimentation deletes and enforcement
keeps.

### What was not taken

Their extensive-game framework, ordinal payoffs, enforcer and sanction sections,
and the **retarded preconditions** of folio 216 — `φ → ⟨¬viol | a⟩⊤` and
`φ → [viol | a]⊥`, permitting an action only along its non-violating outcomes.
That last is a third mode, neither forbidding nor permitting outright, and it
needs an outcome-conditioned action modality this repository does not have.

This module has no payoffs at all, so what is taken from print is the **axis
claim** and not the game transformation. Recorded so that nobody later reads
`enforce` as carrying their deterrence result.

## The safety-relevant consequence

`InstitutionalSetting.exists_empowered_possible_not_permitted`: an act can be
institutionally effective **and** practically possible **and** not permitted.
A check that tests whether an action can be performed, or whether it counts, or
both, has not tested whether it is allowed.

`oughtImpliesCan_does_not_give_permission` blocks the adjacent bad argument —
that because a system must do something and can do it, it may. The obligation
exhibited is the weakest one that could be accused of triviality ("whatever can
be done, must be"), which is exactly the case where ought-implies-can holds by
construction and still buys no permission.

## Where the power axis already lived

`Forces` and `effectivity` in `AISafetyAtlas.Sovereignty.Separations` are
**practical possibility** in Jones & Sergot's sense — what a coalition can bring
about — *not* institutionalised power. Their abstract exists to prevent exactly
that conflation, and it is recorded here because the atlas had both notions in
the tree under names that do not distinguish them.

## Prior-art search — done 2026-09-13, after the build, which was the wrong order

Recorded because [`lean-reuse-sources.md`](../agent/policy/lean-reuse-sources.md)
asks for it *before* building and this search happened after. The outcome did
not change what was built, but that is luck rather than method.

| Where | Searched for | Found |
|---|---|---|
| Local `.lake/packages` (Mathlib, Foundation, Cslib absent, Causalean, PFR, batteries) | `deontic`, `effectivity`, `counts-as`, `permitted` | **Nothing.** The vendored `Foundation` has `Propositional`, `FirstOrder`, `SecondOrder` and no modal or deontic tree |
| lean-explore (Mathlib + indexed packages) | deontic logic, obligation, permission, normative system | `Cslib.Logic.Modal` carries normal modal systems including `D4`, and `Arxiv.«1308.0994».NormalModalLogic`. **Not vendored here**, and a normal modal logic is not this module's object |
| AFP, *Logic / General logic / Modal logic* | `deontic` | **No results** |
| AFP, *Mathematics / Games and economics* | effectivity functions, core stability | **Nothing.** The topic holds Arrow, Gibbard–Satterthwaite, Sen, randomised social choice, SDS impossibility, stable matching, Gale–Shapley, Gale–Stewart games — no effectivity functions and no Keiding |
| Web | dyadic deontic logic in Isabelle/HOL | **Real prior art exists**, see below |

### The prior art that does exist, and why it was not used

Benzmüller, Farjami and Parent have Isabelle/HOL **shallow semantical
embeddings of dyadic deontic logics** — Carmo & Jones's, and Åqvist's system
`E` — proved faithful (sound and complete) and usable as automated provers for
those logics.

That is genuinely the state of the art and it is **not this module's object**.
This module is deliberately *not* a deontic logic: no `O`, no `P` operator, no
modal axiom, no semantics, no inference relation. Porting an embedding of
Carmo–Jones or Åqvist `E` would be answering a different question — "which
deontic logic does the atlas adopt?" — which is still open and is the user's to
take. If that question is ever answered yes, **those embeddings are where to
start, and this note is the pointer.**

Nothing was found for Keiding's stability condition or for Jones & Sergot's
counts-as connective in any prover. `LAND-SOV-STABILITY-001` and
`LAND-SOV-INSTITUTION-001` are builds because there was nothing to reuse, and
that is now checked rather than assumed.
