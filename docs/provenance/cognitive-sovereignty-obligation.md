# Cognitive sovereignty: one obligation, stated

**Status.** Specification, 2026-09-08. No row is claimed and nothing here is
coverage. It exists because the next increment on this concept would otherwise be
a choice of infrastructure argued from resemblance, and the honest first move is
to state one obligation precisely enough that a substrate can be *tested* against
it rather than *matched* to it.

**Lean.** `AISafetyAtlas.Sovereignty.Separations` carries the countermodels and
the separation result. It is not a foundation — every definition in it is
consumed by a theorem in the same file — and §6 says exactly which of this note's
claims are machine-checked and which are still prose.

**What this replaces.** An earlier scoping argument in this session mapped the
concept onto shipped primitives by resemblance — superadditivity as a
"conservation law", indistinguishability as shadow sovereignty, attenuation as
resistance to coercion — and asserted coverage without writing the implication
arrow. Section 4 discharges each of those, negatively, with the counterexamples.

## 1. Why an obligation, and not a definition

Three definitions of *cognitive sovereignty* exist in the source author's
published work, and none of them is gradeable as written:

| Text | Definition | Pin |
|---|---|---|
| Glossary, from *The Memory Wars* | "the ability of individuals, groups, and nations to maintain autonomous thought and preserve identity in the age of powerful AI systems" | arXiv:2508.05867; coinage ledger carries first-publication URL, ISO date, Wayback, SHA-256 |
| *The Power Gambit* Pt 2 | "the ability to maintain autonomous thinking, decision-making, and amplified acting" | `/writing/ai-alignment-framework-seal-reaim-tune/` |
| HEC2026 keynote notes | "the capacity to remain the **author** of your own memory, goals, judgment, and action when those are increasingly mediated by AI", with five verbs — preserve, inspect, contest, redirect, recover | **unpublished, and since 2026-09-12 pinned**: a private note, sha256 `a37f19eab28e7e228aeae8b85983937ee83806f24f8993bbc322e3670a949ad3` |

The first two have no operational content. The third has it and is not
published. **Amended 2026-09-12:** the third is now *pinned* — the keynote
notes are held privately with a sha256, alongside the working files that
accompany them. Pinned is not published: the five verbs remain ungradeable
*against print*, and no row may claim coverage of them. What changes is that
atlas-side interpretation of them can now be checked against a fixed document
instead of against a recollection — the same standing this repository gives the
unpublished power proposal. The five verbs appear verbatim in that document at
its paragraph on what remaining the author unpacks into, and again in its
closing test: *preserve, inspect, contest, redirect, recover*, asked of Memory,
Compass and Engine in turn.

So this note does not grade anything against a definition. It states one
**obligation** that any of the three would have to imply, and treats that as the
test object. If the operational cut is later published, the obligation becomes
checkable *against print*; until then it is an atlas-side statement of intent and
is labelled as one.

The obligation chosen is the one the source author raised as the objection that
motivated this note: sovereignty is defined relative to other agents who are
pushing their own will, and the question is how much of its course the pressured
party keeps.

## 2. SOV-1, stated

Fix a set of agents `N`, a strategy space `strategy : N → Type`, an **outcome
type** `X`, and an **outcome map**

    g : (∀ i, strategy i) → X

For a coalition `C ⊆ N` and a set `A ⊆ X`, write

    Forces(C, A)  ≔  ∃ sC, ∀ s₋C,  g (sC ⊕ s₋C) ∈ A

— `C` has a joint strategy landing the outcome in `A` whatever the complement
does. The **effectivity family** of `C` is `E(C) ≔ { A | Forces(C, A) }`.

`Forces(C, A)` alone says nothing about sovereignty: in a game where one agent
names the outcome by itself, every other agent still satisfies `Forces({i}, X)`
by the safety condition and has no power at all. Three further pieces are needed,
and the first is a hole rather than a choice.

1. **Whose strategy is existentially quantified.** This is the blocking question.
   In the delegated game the principal has **no strategy slot** — the agent holds
   it — so `Forces_{g₁}({p}, A)` as written is *undefined*. Three repairs, and
   they are materially different obligations:
   - the delegate joins the existential coalition — **assumes its cooperation**,
     so this measures the principal-plus-agent bloc against outsiders;
   - the delegate sits in the universally quantified complement — demands the
     guarantee hold **even against the delegate's own deviation**, the strongest
     reading and the one closest to "shadow sovereignty";
   - the delegate's policy is fixed as part of the game form — the principal
     forces nothing, and the question becomes which `A` the fixed policy lands in.

   Nothing below picks one. Until one is picked, SOV-1 is a schema, not a
   statement. This supersedes the earlier framing that treated the baseline's
   type as the open problem.
2. **A protected set.** `A` is not arbitrary — it is what the principal is
   entitled to hold. Nothing in the game form supplies it; it comes from the
   mandate. This is where MCE's *Compass* enters, and it is an input, not a
   theorem. Write `𝒜` for the declared family of mandate-relevant targets.
3. **A comparison, and not a scalar.** Sovereignty is retained or lost relative
   to a baseline game `g₀ : S₀ → X` against the delegated `g₁ : S₁ → X`. The two
   need **not** share a profile type: both effectivity families live in
   `Set (Set X)`, and that is where the comparison happens. What does need
   justification is that the two games carry the same outcome interpretation and
   that the controlling coalitions correspond.

   The comparison is a **partial order**, not a number:

       E₀(C₀) ∩ 𝒜  ⊆  E₁(C₁) ∩ 𝒜

   — every mandate-relevant guarantee the principal had, it still has. Coarsening
   cannot be assumed in general: delegation may gain some guarantees and lose
   others, leaving the two families incomparable.

**A retraction.** An earlier draft proposed the *fineness* of `E(p)` — the
smallest forceable set, in units of `log |·|` — as the retention measure. It does
not work. Compare a principal in a system permanently fixed at outcome `x` with a
principal who can select any outcome: both force a singleton, both have minimum
forceable cardinality one, and taking a logarithm preserves the failure. Minimum
cardinality measures *precision*, not *choice*. Ashby's counting is not thereby
irrelevant, but it attaches elsewhere — to the **surjectivity** of the target map
in `exists_strategy_forcing`, which is exactly what separates those two cases —
and a numerical measure is deferred rather than proposed.

**SOV-1 (schema).** *Given a mandate family `𝒜`, a baseline game `g₀` and a
delegated game `g₁`, and a resolution of item 1 fixing which coalition `C₁` acts
for the principal in `g₁`: the principal retains its mandate when
`E₀(C₀) ∩ 𝒜 ⊆ E₁(C₁) ∩ 𝒜`.* This is an ordinary proposition once item 1 is
resolved; what it is not is a single forcing claim.

This is the smallest statement that carries the objection. It is deliberately not
the whole concept: it addresses the *redirect* verb and part of *recover*, and
says nothing about *preserve*, *inspect* or *contest*.

## 3. What the atlas already has of it

`AISafetyAtlas.Control.exists_strategy_forcing` is

    ∃ c : C, ∀ d : D, T d (f c d) = e

which is `Forces({controller}, {e})` — the SOV-1 shape at singletons, with
outcome type `E` genuinely distinct from the strategy types, and outcome map
`fun c d => T d (f c d)`. The atlas therefore already states the forcing
predicate, for a two-party game form in which the complement is a *disturbance*:
a range with no payoff and no budget.

That is not a rewording. It fixes what is actually missing, which is smaller than
"a game theory layer":

| SOV-1 needs | Atlas status |
|---|---|
| outcome type distinct from strategies | present (`E` in `CompleteControl`) |
| outcome map | **admitted, not supplied** — the composite above, over `C × D` |
| `∃` own strategy, `∀` complement strategy | present |
| `A` an arbitrary set, not a singleton | **free, not missing** — see below |
| complement is an agent with its own payoff | **not required** — see below |
| coalitions rather than one controller | **absent** |
| baseline/delegated comparison | **absent** |

Two things that table hides, and they matter for §5. There is **no `outcome`
field**: the outcome is the composite expression `fun c d => T d (f c d)`, and
the `g : C → E` appearing in `IsPerfectRegulator` is the *target* map, not the
outcome map — the module says so explicitly ("targets *are* outcomes, which is
`g = id`"). And the regulator `f` is a **fixed function, not a player**, so the
strategy profile here is `C × D` — the two-player case — with `R` supplied rather
than chosen. Both are admissible for SOV-1 (`C × D` is a profile type, and the
composite is definable in a line) but neither is supplied, and a general
formulation has to pay for them.

Two entries in that table correct an earlier draft that overstated the gap.

**Arbitrary targets are free.** `exists_strategy_forcing` is stated at a singleton
`{e}`, but forcing every singleton gives forcing every *non-empty* `A` at once:
choose `a ∈ A` and force `{a} ⊆ A`. So generalizing the target set is a corollary,
not a capability. The substantial generalization is in the other direction —
**partial control without perfect regulation**. The theorem's hypotheses are
`IsPerfectRegulator T f g` *and* `Surjective g`; sovereignty is interesting
exactly where one or both fail, and nothing in the tree speaks to that regime.

**The complement's payoff is not required.** `∀ s₋C` already dominates any choice
the complement might make for any reason, so α-forcing needs no opponent utility.
An earlier draft gave "the pusher has its own payoff" as the reason SOV-1 must
enter the strategic register. That reason was wrong. The register question
survives on different grounds — forcing is an *ability* claim, which is what the
recorded ranking in §7 is about — but it is not about payoffs.

`Control.card_disturbance_le_card_regulator` and the `ashby_*` counting results
supply the unit for item 3 of §2 and need no change.

## 4. What does not discharge SOV-1

Each of these was proposed in scoping and each fails, with the reason.

**Superadditivity of an effectivity function.** `X ∈ E(C), Y ∈ E(D), C ∩ D = ∅ ⟹
X ∩ Y ∈ E(C ∪ D)` is a *playability axiom*, not a protection guarantee.

*Countermodel.* Two players `p` (pressured) and `q` (pusher). Let `X` be the
outcome type, `strategy q ≔ X`, `strategy p` any non-empty type, and
`g (s_p, s_q) ≔ s_q` — the pusher names the outcome outright. Then
`E(p) = {A | X ⊆ A} = {X}`, `E(q)` is every non-empty `A`, and every playability
condition including superadditivity holds. The pressured player forces **no proper
subset of `X`**. So the axiom holds under complete domination.

The `g (s_p, s_q) ≔ s_q` specification matters: for a general `g` that merely
ignores `s_p`, the weak family is `{A | range g ⊆ A}`, which equals `{X}` only
when the pusher can reach every outcome.

**Regularity.** The sharper consequence — superadditivity *plus* liveness gives
`X ∈ E(C), Y ∈ E(Cᶜ) ⟹ X ∩ Y ≠ ∅` — rules out two parties forcing *contradictory*
outcomes. It does not rule out domination, and in the countermodel above it is
vacuous precisely because the weak party's only forced set is `X`, which meets
everything. Consistency is not retention.

The next two are **separation arguments, not countermodels.** They say why an
implication is not available; neither is yet a constructed model with both
properties evaluated, and each is owed one before it is cited as a refutation.

**Indistinguishability.** Reward/planner unidentifiability and the knowability
kernel concern what an observer can *determine* from a trace. SOV-1 concerns what
a principal can *preserve*. Neither direction is available for free: a principal
may be unable to tell which of two principals its agent serves while still forcing
`A`, and may be certain it is being dominated while forcing no proper subset. The
two-principal check is worth running on its own merits, but its result is an
**informational** statement and must be labelled as one. §8 item 3 owes the
countermodel.

**Attenuation.** `child.authority ⊆ parent.authority ∧ ∀ r, child.budget r ≤
parent.budget r` bounds what a delegate holds *under the stated grant rules*. It
is silent about an agent outside the delegation tree pushing on the same outcome,
which is the whole of SOV-1's `∀ s₋C`. Attenuation belongs to a different
obligation — call it SOV-2, "no delegate exceeds the mandate" — which is worth
stating separately and is not this one.

**Ashby complete control.** This one is not a failed candidate but a partial one.
It supplies a **sufficient forcing instance** — `Forces({controller}, {e})` with a
preferenceless complement — under two hypotheses, `IsPerfectRegulator T f g` and
`Surjective g`. It supplies no baseline, no comparison and no retention measure,
so it discharges the forcing half of SOV-1 and none of §2 item 3. A special case
to generalize, not a competitor, and the generalization that matters is dropping
its hypotheses rather than widening its target.

### `cl-lean`, opened rather than surveyed (2026-09-10)

The row above records a verdict on whether the tree may be *used* -- unlicensed,
Lean 3 -- and stops there. That is not the same as knowing what is in it, and the
difference cost something. `AISafetyAtlas.Sovereignty.PlayableConverse` was built
refuting Pauly's Theorem 3.2 as though the refutation were new; it is Goranko,
Jamroga and Turrini's, published in 2011 and 2013. **The first fifteen lines of
`src/semantics/playability.lean` name that paper**, and this repository had been
citing that file as the source of "truly playable" for two days without opening
it.

What is actually in the tree, read 2026-09-10 from a clone at `depth 1`:

* 28 Lean files, all of them modal logic -- syntax, semantics and soundness for
  CL, CLK and CLC. A search for `game form` or `strategic game` across `src/`
  returns one line, and that line is a bibliography entry. **There are no game
  forms in it**, so no representation theorem and no counterexample. Nothing this
  atlas built duplicates it.
* `effectivity_struct` is *state-indexed*, `states → set agents → set (set states)`,
  because it is Kripke semantics. The atlas's `Playable` takes a bare
  `Set N → Set (Set X)`. The five conditions line up nearly clause for clause,
  which is two faithful transcriptions of Pauly page 152 and not a common source.
* Two results the atlas did not have: `playable_from_semi_Nmax_reg` (semi-playable
  plus `N`-maximality plus regularity gives playability) and
  `truly_playable_from_finite` (a finite state type gives the principal element).

The second is now `AISafetyAtlas.Sovereignty.TrulyPlayable`, proved from the
Goranko-Jamroga-Turrini paper and **stated more widely than either**: the argument
consumes only a minimal element of the family `E ∅`, so a finite family suffices
and a finite outcome type is two corollaries down. It is that paper's
**Proposition 6**, which this note also failed to say until 2026-09-10.

**The first is still not built, and the reason given here for not building it was
wrong. Retracted 2026-09-10.** This paragraph said *"`cl-lean` cites three papers
and does not say which owns `semi_playable`, and Ågotnes and Alechina are not
pinned. A formalization repository is not a source."* The last sentence is right
and the conclusion drawn from it was not. Semi-playability is **Pauly's own**:
§3.3, page 155 of the paper this cluster was already built from, where he defines
it as the four conditions restricted to coalitions `C ≠ N` and proves

> **Lemma 3.4.** An effectivity function `E` is playable iff it is semi-playable,
> regular and `N`-maximal.

which is `playable_from_semi_Nmax_reg` exactly. The provenance was never in doubt;
it was in the pinned source, unread, because Pauly had no section in the coverage
audit and `AISafetyAtlas.Sovereignty.Playability` had no registry row until
2026-09-10. Both now exist — section 15 and `LAND-SOV-PLAYABILITY-001` — and
Lemma 3.4 is the cheapest open item in this cluster.

**That is the second retraction of this exact shape in one day**, the first being
Proposition 6 above. Both were absence claims about a *source* settled by reading
a *repository*, and in both cases the source was pinned, in hand, and says the
opposite. The rule below was written for the first; it did not prevent the
second, because it is about candidate rows and these were about coverage
sections. The guard added on the same day —
`scripts/check_coverage_audit.py`'s module-ledger check — is aimed at the
recurrence rather than at either instance.

**The rule this changes:** a candidate row may record "unusable" only alongside
what the tree contains. Opening the file costs a clone; not opening it cost a
misattributed result that had to be retracted after it was committed.

## 5. The test this sets for a substrate

A candidate substrate is adequate for SOV-1 iff it supplies, or cheaply admits:
(a) an outcome type distinct from the strategy profile; (b) an outcome map;
(c) quantification over the complement's strategies; (d) a comparison between two
effectivity families over the same outcome type.

Measured against that, as of 2026-09-08:

| Candidate | (a) | (b) | (c) | (d) | Licence / toolchain |
|---|:-:|:-:|:-:|:-:|---|
| `EconCSLib.GameTheory.StrategicGame` | ✗ | ✗ | ✓ | ✗ | Apache-2.0; Lean v4.30.0 vs atlas v4.33.0 |
| `AISafetyAtlas.Control.CompleteControl` | ✓ | ≈ | ✓ | ✗ | in tree |
| `kaiobendrauf/cl-lean` (CLC, ITP 2024) | ✓ | ✓ | ✓ | ✗ | **no LICENSE on any branch**; Lean 3 (`leanprover-community/lean:3.42.1`, mathlib3 `fe0c4cd9`) |
| Delegation games (Sourbut et al., IJCAI 2024) | ✗ | ✗ | ✗ | ✗ | model, not a library |
| `Causalean` (in `CausalSmith`) | — | — | — | — | no decision/utility partition; not a game form |

`StrategicGame` is `strategy : N → Type*` together with `payoff : (∀ i, strategy
i) → N → U` and, per its own docstring, "records only the bare data: strategy
spaces and a payoff function". Outcomes there are profiles unless an outcome map
is supplied. That is a design decision SOV-1 forces into the open, and it is the
reason "define effectivity over EconCSLib's game form" is not free.

## 6. What is machine-checked, and what is still prose

`AISafetyAtlas.Sovereignty.Separations` discharges four of this note's claims.
It is not a foundation and not coverage: every definition in it exists to state a
theorem in the same file, and nothing outside is meant to build on `GameForm`.

| Claim | Status |
|---|---|
| Superadditivity carries no information about domination | **checked** — `forces_superadditive` proves it for *every* game form, and `dominated_forces_univ` gives one in which the pressured player forces no proper subset. An axiom nothing can fail distinguishes nothing. |
| Widening the target is free | **checked** — `forces_of_forces_singletons` |
| The three readings of §2 item 1 are three obligations | **checked** — `retainsAgainst_imp_retainsWith` is the only implication; `not_retainsAgainst_delegateDecides` and `not_retainsUnder_delegateDecides` refute the others |
| Minimum forceable cardinality is not a retention measure | **checked** — `minCard_cannot_separate` |
| Indistinguishability does not give retention | **prose** — §8 item 3 owes the countermodel |
| Attenuation does not give coercion resistance | **prose** — §8 item 3 owes the countermodel |

Two further results were added on 2026-09-09 after a literature scan, and both
change what this note claims.

**`Forces` is α-power, and the literature has the other half.** Chen, Ju &
Ågotnes (arXiv:2607.10567, 2026-07-12; two-agent precursor arXiv:2603.04160)
distinguish α-power from **actual power**: the coalition has an action such that
*(1)* it forces the outcome into the set and *(2)* every outcome in the set is
compatible with that action. Clause (2) is what α lacks. `ActualPower` states it,
`ActualPower.forces` shows it is strictly stronger, and
`pinned_not_actualPower_pair` separates them.

This **relocates `forces_of_forces_singletons`**. §3 called widening the target
"free" and treated that as a fact about `exists_strategy_forcing`. It is not
specific to this development at all: α-forcing is upward closed by construction,
and the resulting inability to distinguish an exactly-hit target from a
merely-landed-in one is the standard objection to α-effectivity, which the paper
attributes to van Benthem. The atlas was rediscovering a known limitation.
*Source status:* both definitions are transcribed from the arXiv abstract, which
states them in full; the representation theorems have not been read and nothing
here depends on them.

**Mediated forcing, and the monotonicity the concept needs.** A game form cannot
express mediation — its strategies are bare choices with nothing to condition on.
`MediatedForm` adds `obs : W → O` and `result : W → Act → X`, and `MForces`
quantifies a *plan* `O → Act` existentially against every state universally.
`mforces_of_factors` proves that if `obs' = k ∘ obs` — the coarse channel tells
the principal no more than the fine one — then everything forceable under `obs'`
is forceable under `obs`. **Coarsening a channel never gains; refining never
loses.**

It holds for every `result`, with no assumption about the world's intentions,
because `∀ w` already covers an adversarial state. And it is not vacuous:
`matchGame_forces` against `matchGameBlind_not_forces` exhibits a channel where
the loss is real.

This is the smallest true statement of "sovereignty is lost to mediation", and it
is closer to the concept's published definition — *mediated* by AI, not
*delegated* to it — than the delegation reading in §2 item 1. Delegation remains a
real obligation; it is no longer obviously the primary one.

The separation result changes the standing of §2 item 1. It was recorded as a
choice to be made by fiat; it is now a choice between three inequivalent
obligations, with the inequivalence proved rather than asserted. Reading 2 is
strictly stronger than reading 1, and reading 3 is comparable to neither.

## 7. What this note does not claim

- It does not claim SOV-1 is *the* definition of cognitive sovereignty. It is one
  obligation the concept implies, chosen because it carries the objection.
- It does not claim the published definitions imply SOV-1. They are too coarse to
  imply anything; that is why §1 exists.
- It does not authorize a dependency, a module, or a registry row.
- It does not reverse the recorded ranking in the sibling notes tree
  (a private note §8, carried to
  `ROADMAP_IDEAS.md:266`) that places an ability operator last on the grounds
  that it leaves the informational register `M0` marks. That ranking had one
  speculative consumer; there are now three — this obligation, corrigibility, and
  the absent delegation layers — which is an argument to re-run the ranking, not
  a result that changes it.

## 8. Open

1. Publish the operational cut, or accept that the five verbs are atlas-side
   interpretation and grade them as such.

   **Answered, 2026-09-13:** the maintainer states that he is the author of the
   term and therefore judges sameness and partness for it. Under the settled
   self-sourcing precedent — the `BY-*` rows are his own survey — the five-verb
   cut may be graded as his own reading of his own term rather than as
   third-party interpretation. Two things that does **not** change: the source
   is still unpublished, so rows carry a sha256 pin and no locator,
   the same standing as the power proposal; and it builds nothing, so *inspect*
   and *contest* still have no object.
2. ~~Does Sourbut, Hammond & Wood, *Cooperation and Control in Delegation Games*
   (IJCAI 2024) represent SOV-1?~~ **Closed, 2026-09-08: no.** §3 states
   *"we make the simplifying assumption that there is a one-to-one correspondence
   between principals and agents, and that each principal delegates fully to their
   corresponding agent (i.e. only agents can take actions)."* Definition 4 is
   `D = (S, u, û)` — one strategy space `S`, an agent game `G := (S, u)` and a
   principal game `Ĝ := (S, û)`. Principals have preferences over the agents'
   strategies and **take no actions**, so retained principal intervention, veto and
   revocation are outside the model, and there is no outcome type distinct from
   `S`. It measures alignment (preference similarity) and capability, not forcing.
   It is the right comparison model and not the specification.

   A first reading of this note claimed the paired `(G, Ĝ)` was "half" of test
   (d). **That was wrong.** `G` and `Ĝ` change *whose utilities evaluate the same
   agent actions*; they do not change *who controls* those actions. Over one
   strategy space with one outcome map the two effectivity families coincide, so
   the pairing supplies no before/after authority comparison at all. What the
   paper does supply is evidence for §2 item 1: it is a worked setting in which
   the principal has no slot, and it declines to give it one.
3. The two-principal check against reward unidentifiability, stated as an
   informational result, together with a **countermodel** — a single game in which
   the two principals are indistinguishable and the forcing families differ, and
   one in which they are distinguishable and the families agree. §4 currently owes
   both.
4. A numerical measure on `E(p)`. **Deferred, not proposed** — the minimum-
   cardinality candidate is retracted in §2, and the partial order there is what
   the note commits to. A scalar, if one is wanted later, has to separate the
   fixed-outcome principal from the free-choosing one, which cardinality does not.
5. **Specify principal authority in both games.** This replaces an earlier item
   that treated `g₀`'s profile type as the open question. The type is not the
   problem — both families live in `Set (Set X)` and can be compared there, and
   replacing a slot's owner versus adding a trivial slot may well describe
   equivalent game forms. The problem is §2 item 1: which coalition acts for the
   principal in `g₁`. Fix that in both games, and the rest of SOV-1 is stated.

   **Closed, 2026-09-13, by maintainer ruling rather than by a proof.** The
   coalition is not a free modelling choice: it is fixed by the delegate's
   alignment. An aligned delegate acts for the principal, so the coalition is
   `{p, d}`; an unaligned one does not, so it is `{p}` and the delegate's
   strategies join the complement the guarantee has to survive.
   `AISafetyAtlas.Sovereignty.principalCoalition` carries the rule at an
   arbitrary alignment proposition — deliberately not a decidable one, since the
   case that matters is the one the principal cannot evaluate — and
   `AISafetyAtlas.Sovereignty.SOV1` is `RetainsFamily` at it. So **SOV-1 is now
   a statement, not a schema.**

   Two things that ruling buys.
   `AISafetyAtlas.Sovereignty.sov1_of_retainsFamily_singleton`: discharging
   SOV-1 as though the delegate were unaligned discharges it at *every*
   alignment, so refusing to assume alignment costs nothing and assuming it is
   what costs something. And
   `AISafetyAtlas.Examples.Sovereignty.sov1_turns_on_alignment`: one principal,
   one mandate, one pair of games, holding at the aligned setting and failing at
   the unaligned one — so the parameter is load-bearing and not a relabelling of
   a single obligation.

   Reading 3 is **not** folded in. A pinned delegate policy is a restriction of
   a strategy set and not a coalition, so
   `AISafetyAtlas.Sovereignty.RetainsUnderFamily` is stated in parallel.

## 9. What landed on 2026-09-10, and the two decisions behind it

**Item 1 of §2 is resolved by having been built already.** The three repairs are
`AISafetyAtlas.Sovereignty.RetainsWith`, `RetainsAgainst` and `RetainsUnder`, and
`AISafetyAtlas.Examples.Sovereignty.Separations` separates them: reading 1 holds
on the delegation, reading 2 fails, and reading 3 holds at one fixed policy and
fails at another — so reading 3 is a claim about the *policy*, not about the
principal. A second construction of the same three was started this day and
discarded on finding them; the schema was already a statement three times over,
and this note had not said so.

**Two things were genuinely missing and are now in
`AISafetyAtlas.Sovereignty.Mandate`.**

1. **The published anchor.** `Represents` is Bezalel Peleg, *Effectivity
   functions, game forms, games, and rights*, Social Choice and Welfare 15:
   67-80, **Definition 3.4** — *"A (legal) GF `Γ` is a representation of the
   constitution `⟨ρ, α, γ⟩` if `E_α(·; Γ) = E(·)`"* — read from rendered images of
   pages 72 and 73, because the manifest records that this file's mathematics is
   AMS-glyph and text extraction mangles it. Print's Definition 3.3 is
   α-effectivity, and it is this repository's `Forces` and `effectivity` already.
   Three differences from print, none a strengthening: print restricts to
   `S ≠ ∅` and stipulates `E_α(∅; Γ) = A`, print assumes the outcome function
   surjective, and print's page 73 writes `E_α(S; Γ) = {B ⊆ S | …}` where `B ⊆ A`
   is meant. **Superseded 2026-09-20**: the constitution `⟨ρ, α, γ⟩` is now
   `AISafetyAtlas.Sovereignty.Constitution` and Definition 3.4 is `Represents`
   against it, so `Represents` no longer stands a second game form in for `E`.
   Print's **Theorem 3.5** — a GF with a prescribed α-EF exists iff `γ` is
   monotonic w.r.t. the alternatives and `E` is superadditive — is still not
   proved: `Represents.superadditive` is the necessity of its second condition
   and the sufficiency direction is print's appendix construction.
2. **The mandate family.** The three readings each take a single target set;
   §2 item 3 asks for a family `𝒜` and a comparison between two games.
   `RetainsFamily` is that, `retainsFamily_of_effectivityEq` places SOV-1
   strictly below the comparison of two game forms, and
   `effectivityEq_of_retainsFamily_univ` shows the two meet at the extremes — so
   SOV-1 is a weakening of a published condition rather than a notion of its own.
   `retainsFamily_of_represents` is the same specialization against Peleg's
   Definition 3.4 itself.

**Decision on §8 item 1, taken 2026-09-10:** the five verbs are **atlas-side
interpretation** and are graded as such. They are not claimed to come from a
published source; the only operational cut is unpublished. The rights layer in
`AISafetyAtlas.Sovereignty.Rights` is what this cluster grades against print —
`Constitution`, `Represents` and the conditions around them — and the mandate
family, the comparison and the three readings are all this repository's reading
of a concept
whose published definitions §1 already calls too coarse to imply anything.

**A library-wide concept work order was written on 2026-09-12** at
the private manifest of 2026-09-12,
sha256 `7367d2049f8bd8fb752d03a82ccc290f40992f22c2205a0600e1d78eba78df3e`. It
lists every concept across the atlas carried as an uninstantiated parameter or
an admitted gap, with what each blocks and what to fetch. Items 1, 7 and 8 —
institutional power, capability decay and contestability — are the three that
bear on this note, and item 7 and item 8 are *preserve* and *contest*.
**Updated later the same day:** every fetchable item on it has been supplied.
Fifteen works are pinned in
the private manifest of 2026-09-12,
sha256 `b4f4e264ac4c791afcc6754ad157eebb439e8f15e213b50552a5b6434808e37e`, which
also hashes the HEC2026 working files. **Four have since been read** —
Jones & Sergot, Halpern & Moses, Keiding, and Herzig & Lorini from its text
layer only — and three more (Clarkson & Schneider, Ramadge & Wonham,
Myers-Sabelfeld-Zdancewic) in the private manifest of 2026-09-09. **None of
them backs a row in this note and none is coverage.** One item from that reading
bears directly here: Clarkson & Schneider p. 1161 defines `HP = P(P(Ψ_inf))`
with satisfaction `T ⊨ H ≜ T ∈ H`, which is the type and the membership test
`AISafetyAtlas.Sovereignty.CogSov` already uses.

**A correction that belongs in this note, since it was made here first.** When
that reading was recorded I wrote that the atlas *had no hyperproperty layer*.
It has one, it has had one since before this note existed, and it cites the same
paper: `AISafetyAtlas.Compositional.Hyperproperties`, with `LAND-HYPER-002`
carrying Clarkson-Schneider Theorem 2 in two presentations and a `PrefixTopology`
submodule proving closed and dense mean hypersafety and hyperliveness. My search
covered `AISafetyAtlas/Sovereignty/` only. So the standing gap is not a missing
layer but a **missing transport** between two modules that already use the same
type. Whether `H` should also be required *subset closed* — their `SSC`, the
exact class for which refinement transfers — is open, is not decided here, and
is the one thing the paper has that **neither** atlas module carries.

**Still open.** SOV-1 addresses *redirect* and part of *recover*. **Nothing here
touches *preserve*, *inspect* or *contest*** — three of the five verbs have no
formalization. **Amended 2026-09-12:** they now have a pinned source to
formalize *against*, which they did not before; what they still lack is a
published one, so anything built there is interpretation and is labelled as
interpretation. The nearest existing material is
`AISafetyAtlas.Sovereignty.Auditability` for *inspect* — `C9`'s exact
auditability is the observation-fibre condition an inspection right would have
to imply — and `AISafetyAtlas.Sovereignty.Belief` for the failure mode
*contest* is meant to prevent. The constitution object landed on 2026-09-20 in
`AISafetyAtlas.Sovereignty.Rights`; Peleg's Theorem 3.5 is still the natural
next result, and only the necessity half of it is proved.
