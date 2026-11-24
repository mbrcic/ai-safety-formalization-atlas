# Scope grading: how a Lean rendering is graded against a printed statement

Specification v6, adopted 2026-11-22 for v0.10.0. The working copy and its review history are
in `docs/provenance/regrade-2026-11/spec/`; the mapping from the old labels is
`docs/provenance/regrade-2026-11/spec/MAPPING-to-v6.md`.

This is the Atlas's scope taxonomy. It replaces the single Scope scale of the coverage audit's
preamble (Wider / Same / Narrower / Mixed / Beyond, read as "does the atlas statement imply the
printed one") and SPEC v5. The five scope values survive as **computed outputs** (§6); what is
graded is three axes, **C objects**, **A applicability** and **B conclusion**, each with a test.

Changes from v5 (from the two reviews in `docs/provenance/regrade-2026-11/spec/reviews/` and the regrade's rulings):
refuted print and repairs (§7.7); one spelling for "nothing proved" (§6); roles `conjecture` and
`no-print` (§7.5); a general rule for several readings (§7.6); carrier generalization with polarity
and the representation reduction (A6, A10, §7.1); strictness and recovery tests (A11, A12, B5);
joint extension for interfaces (A7); premise proxies (C3); per-component union of routes (§7.3);
a closed list of non-Lean steps and the `argued` flag (§0, §7.9); rulings with general force (§8);
defect records and remedies (§9); the change rule that replaces "Stability" (§10); what the audit
table records (§11); calibration E9, E19, E22, E23 corrected and E27-E38 added (§12). Second round
(after `docs/provenance/regrade-2026-11/spec/reviews/2026-11-22-spec-v6-review-*.md`): whole-row certification of every label (§6);
the transfer test replaces truth-preserving maps (§7.1, A6); empty overlap gives B = none (K5);
direction-shown rules (A11, B5); polarity by parity (A10); an order for conservative readings (§7.6);
role tests (§7.5); bounded argued steps on all axes, with a headline column (§7.9, §6). Third round
(after `docs/provenance/regrade-2026-11/spec/reviews/2026-11-22-spec-v6b-review-*.md`): certification by forward and reverse
entailment, with recovery (§6); the transfer test needs a map φ through print's conclusion (§7.1);
vacuity (K5) separated from conditional renderings; substantive Partial (K6); proxies give `missing`
(B1); quantifier-aware polarity (A10); shared witnesses versus shared binders (§7.3); definitions in
the **stated** column (§6); E4, E5, E9, E11, E16, E19, E30 corrected, E39-E40 added.

**Adoption (v0.10.0).** The coverage audit's Scope cells hold the computed scope, and its Coverage
cells are computed from it; `scripts/check_coverage_audit.py` accepts `None` and `Refuted` and fails a
Coverage cell that disagrees with its Scope cell. The per-row axis columns of §11 are not yet in the
table; each row's axes are in the regrade's provenance (`final-grades.tsv` and the v6 adjudication records).

Follow §1 in order. Every label has a test; apply it literally, never by overall impression.

## 0. Vocabulary

- **Print.** The statement as the source states it: objects, hypotheses, conclusion, quantifiers.
  The packet (or the audit row) gives it transcribed from the page with the printed context it
  needs, the source's definitions of its terms, recorded proof excerpts, and the source's standing
  assumptions (the *Setting* block). A grader with page access reads the defining section of each
  term on the rendered page; text beyond the packet is quoted with its page. Where the Atlas
  transcription differs from print, print wins.
- **Print's hypotheses** are (i) what the statement says, (ii) the standing assumptions of its
  section or paper, (iii) what print's terms mean in the source, and (iv) the author rulings that
  apply (§8, register). A silent statement does not make print unrestricted. Never supply (ii)-(iii)
  from memory of the source or the literature; if a decision needs material not shown, say what and
  set `missing_context: true`.
- **Rendering.** The declarations the row cites, taken together (§7.3), read **as elaborated**:
  check `variable` blocks, section instance arguments and `omit ... in`. Support that exists in the
  tree but is not cited is a **citation gap** (§7.8).
- **Object, instance, component.** An object is a mathematical thing print is about or uses. An
  instance is one assignment of objects satisfying a statement's hypotheses. A component is one
  separately checkable part of a conclusion (each inequality, equality, existence clause,
  uniqueness clause, rate).
- **Proved.** Established by a cited or citable Lean declaration without `sorry` under the axiom
  policy, **or** derived from such declarations by steps each on this **closed list**:
  definitional unfolding; instantiation or specialization; rewriting by a named Lean lemma;
  propositional and first-order logic; order antisymmetry and transitivity; arithmetic a decision
  procedure checks (`norm_num`, `decide`, `omega` level); a representation map (§7.1). Every step is
  named in the reason. Any other step ("a standard theorem", "by Fubini", "clearly") makes the
  component **argued**, not proved (§7.9). A Lean hypothesis is never proved.
- **Ruling.** An author's decision on what print means or on an accepted repair. Rulings are part
  of print's meaning, applied exactly like a definition in the source; they are not evidence about
  the Lean. Each has an id, date, text, scope (one source, or general, §8) and a recorded sweep of
  the rows it could decide.

## 1. Procedure

0. **Role** (§7.5): theorem, definition, assumption, conjecture, explanatory, or no-print.
1. **Refutation check** (§7.7). Does a Lean declaration prove print false at an instance meeting
   every hypothesis of print (all four kinds)? If yes, record `refutes: true`; if an accepted repair
   exists, grade the repaired print through steps 2-5 and record both.
2. **Axis C, objects** (§2).
3. **Axis A, applicability** (§3), difference by difference, both directions.
4. **Axis B, conclusion** (§4), component by component.
5. **Consistency** (§5), then **readings** (§7.6): if a reading no ruling settles changes the label,
   grade the conservative reading and record the others.

## 2. Axis C: objects

For each object in print's hypotheses or conclusion, find the Lean object that plays its role. The
row's label is the worst: own < equivalent < proxy.

| Label | Test |
|---|---|
| `own` | The Lean object is print's object, up to representation (§7.1). |
| `equivalent` | Defined differently, and a **proved** statement (§0) shows it equals or corresponds one-to-one to print's object on print's instances. Name it in `reason_C`. |
| `proxy` | Different, with no proved correspondence: truncations, approximations, a similar quantity, a specific instance standing in for print's general object. |

- C0. **Subclass is not proxy.** A special case of print's object is `own`; the restriction is an
  applicability difference (A), judged there.
- C0a. **Abstract parameters.** A Lean parameter or interface where print fixes one object is `own`
  if print's object is a value it can take; state the assignment. Whether print's object meets the
  interface is A7. Generality over the other values is graded by A6 (E22).
- C0b. **Truncation.** Check every value, return or quantity for a depth, horizon or step index. A
  depth-n quantity for a limit quantity is `proxy` unless a proved statement connects them.
- C1. "Equal by a known theorem not in the tree" is `proxy` unless the step is on §0's closed list
  or is an argued step meeting §7.9 (then `equivalent`, flagged `argued`).
- C2. A correspondence proved only under an extra hypothesis is `equivalent` only if that hypothesis
  is print's; otherwise `proxy`.
- C3. **Proxies in hypotheses.** C applies to objects in print's hypotheses too. A proxy there makes
  A `incomparable` (the Lean's instances are about a different object) unless the correspondence is
  proved.

## 3. Axis A: applicability (hypotheses only)

List print's hypotheses and the Lean's (objects translated via C). Classify each difference:

| Difference | Effect |
|---|---|
| Lean drops or weakens a hypothesis print's others do not imply | broadens |
| Lean drops a hypothesis print's others imply | none; `leaner: true` |
| Lean generalizes a carrier, under A6 and A10 | broadens, or none, or as A10 says |
| Lean adds a hypothesis print lacks (an unproved conjecture, an assumed bound or property, a finiteness or regularity condition) | narrows |
| Print is about a specific object; the Lean theorem is general and its hypotheses are never proved for that object | narrows (and the generality broadens: A6, E9) |
| A Lean hypothesis renders a condition print states (quote the phrase) | none |
| A Lean hypothesis is implied by print's hypotheses (state the implication) | none |
| A Lean hypothesis is weaker than the print hypothesis it replaces | broadens |
| A hypothesis replaced by a provably equivalent one, or redundant given the others | none |
| Representation change (§7.1) | none |
| The Lean also admits degenerate instances on which print's conclusion holds trivially | none |

Label: `same` (no effect), `broader` (some broadens, none narrows), `narrower` (some narrows, none
broadens), `incomparable` (both). Record every difference in both directions before labelling.

- A1. An assumed hypothesis narrows even if believed true or a famous conjecture, until proved.
- A2. If the packet lacks the material to decide whether a Lean hypothesis is implied, treat it as
  narrowing and set `missing_context: true`. A2 never licenses narrowing because you did not look.
- A3. The conclusion never influences axis A, except through the degenerate-instance row above,
  the recovery test (A12) and the transfer test (A6, §7.1), which read it by design.
- A4. Dropping a hypothesis broadens only if some instance meets the Lean's hypotheses and not
  print's (a **witness of broadening**, named).
- A5. **Quote before you narrow.** Narrow only with a print instance the Lean excludes in hand, or
  under A1, A2 or A11's second clause (an assumed hypothesis not shown implied), after checking that
  no print phrase, standing assumption, term meaning or ruling implies the hypothesis.
- A6. **Carrier generalization** (any type, field, space or interface value where print fixes a
  specific or finite one), with the carrier universally quantified in a positive position (else
  A10): it is **representation** (no effect) when the **transfer test** of §7.1 passes: every print
  instance is a Lean instance, and the Lean statement follows from the printed statement, taken as a
  hypothesis and not unfolded, by closed-list steps and named Lean transfer lemmas (E19, E27).
  Otherwise it **broadens**, with A4's witness named, and `strict: unknown` unless a reason is given
  why no transfer exists (E2, E22).
- A7. **Interfaces and structure fields are hypotheses.** For print's object, give **one
  simultaneous** extension satisfying every field and axiom together (say how), or name the lemma
  that instantiates the interface. Separate field-by-field checks do not suffice (E29). No joint
  extension for some print instance: narrows, with that instance. Fields that carry data absent
  from print's objects and claim may be filled in any way.
- A8. **Informal premises.** Give the quantified reading and the text that warrants it; never infer
  a stronger premise from the conclusion print argues for. Several readings: §7.6.
- A9. **Graded once.** A restriction on accepted instances is graded on A only, never again as a
  weaker or missing component on B. A subclass narrows only if some print instance lies outside it.
- A10. **Polarity.** The effect of enlarging a class depends on the bounded quantifier over it and
  the parity of that quantifier's position in the whole statement (count the implication antecedents
  and negations it sits under; even = positive, odd = negative). Positive position: a universal class
  enlarged broadens (A6); an existential class enlarged is graded on **B** (B4: the witness may lie
  outside print's class). Negative position: the effects reverse; a universal class enlarged narrows
  (a theorem with hypothesis `∀ x ∈ S, R x` applies to fewer instances when S grows), an existential
  class enlarged broadens (hypothesis `∃ x ∈ S, R x` becomes easier to meet). Shrinking reverses each
  case. A class that a printed `max`, `sup` or `argmax` ranges over is part of the object (C), not a
  carrier.
- A11. **Strictness.** `broader` needs A4's witness. `narrower` needs A5's excluded print instance,
  **or** a Lean hypothesis that print's hypotheses are not shown to imply (an assumed hypothesis,
  A1; E9, E11). Record `strict: shown` when the excluded or extra instance is exhibited and the
  converse fails by a named reason, otherwise `strict: unknown`.
- A12. **Recovery.** A restriction does not narrow if every excluded print instance's conclusion
  follows from the covered instances by steps on §0's closed list (E30: restricting
  `∀ n, P n ∨ n = 0` to `n > 0` loses nothing).

## 4. Axis B: conclusion (on the instances both statements cover)

| Per component | Test |
|---|---|
| `stronger` | Lean's version implies print's and not conversely (tighter bound or constant, extra uniqueness, ∃∀ for ∀∃, an explicit rate where print has none) |
| `same` | equivalent (identical, definitional unfolding, algebraic rearrangement, an explicit witness for print's ∃ meeting B4) |
| `weaker` | print's version implies Lean's and not conversely (looser bound, ∀∃ for ∃∀, fewer conjuncts of the component) |
| `missing` | Lean proves no claim about this component's relation (its quantities combined as print combines them) |
| `incomparable` | Lean proves a claim about this component's relation (or its proxies) that neither implies nor is implied by print's |

A Lean claim counts toward a component only if it is about that component's relation; a claim
about another component's quantities does not make this one `incomparable` (E6).

Row label: `same` (all same); `stronger` (all same or stronger, one stronger, nothing contradicting
print); `weaker` (all same, weaker or missing, one weaker or missing, not all missing);
`incomparable` (one stronger and one weaker or missing, or any incomparable); `none` (all missing).

- B1. A component about a `proxy` object is `missing`: a claim about a proxy is not a claim about
  print's object. (`incomparable` is reserved for claims about print's own or equivalent objects.)
- B2. **Extras.** A fact about print's own component or objects that print's component does not
  already imply counts as `stronger`. A fact about objects print does not mention counts nothing.
- B3. Constructive versus classical proof does not matter.
- B4. **Witnesses.** For an existential or "can" component, one witness establishes it, however
  special, provided (i) it meets every hypothesis of print, standing assumptions included, (ii) for
  each assignment of print's outer parameters one witness meets all jointly bound clauses, and (iii)
  the existential reading is print's (quoted, or by ruling). A witness from a class wider than
  print's (A10) establishes `weaker` unless shown to lie in print's class.
- B5. **Directions.** `same` needs both directions shown. With one direction shown and the converse
  undecided, the label is that direction (`stronger` or `weaker`) with `strict: unknown`. With
  neither shown, the component is `incomparable`. An undecided implication is never `same`.

## 5. Consistency

- K1. A component about a proxy object is `missing` (B1); a proxy in print's hypotheses makes A
  `incomparable` (C3).
- K2. B = `none` gives scope `None` and coverage `No`, whatever A says.
- K3. `refutes: true` without an accepted repair gives scope `Refuted`, coverage `No`; with one,
  the axes grade the repaired print (§7.7).
- K4. `missing_context`, `interpretation_sensitive`, `aggregation_sensitive` or `argued` caps
  confidence at 3 and is shown in the table (§11).
- K5. **Vacuity.** If the Lean's hypotheses are **shown unsatisfiable** at every print instance on
  which print's conclusion is not trivial (no print instance can meet a required interface jointly,
  or an added hypothesis contradicts print's), B is `none`, whatever the axes would otherwise say
  (E39). A hypothesis merely **not shown** for print's instances (an unproved conjecture, a condition
  never checked for print's specific object) is a narrowing under A1 and A11, not vacuity: the row is
  a **conditional** rendering (E9, E11), flagged `conditional: true`.
- K6. **Substantive Partial.** Coverage `Partial` needs at least one print component established
  (`same`, `stronger` or `weaker`) on some print instance whose conclusion is not trivial, possibly
  conditionally (K5). Otherwise B is `none` (E4).

## 6. Computed scope and coverage

| A \ B | stronger | same | weaker | incomparable | none |
|---|---|---|---|---|---|
| **broader** | Wider | Wider | Mixed | Mixed | None |
| **same** | Wider | Same | Narrower | Mixed | None |
| **narrower** | Mixed | Narrower | Narrower | Mixed | None |
| **incomparable** | Mixed | Mixed | Mixed | Mixed | None |

Plus `Refuted` (K3) and `Beyond` (role `no-print`, §7.5). Coverage: `Yes` if Same or Wider; `No`
if None or Refuted; otherwise `Partial`. Wider applicability never excuses a weaker conclusion.

**Certification.** The matrix proposes a label; whole-row entailment certifies it.
- **Forward** (Lean implies print): every print instance is lifted to one Lean instance meeting all
  the Lean's hypotheses simultaneously (C translations, A7 joint extension), or is recovered from
  lifted instances under A12; at each lift the Lean's conclusion implies print's, jointly over
  components that share a witness (§7.3).
- **Reverse** (print implies Lean): the printed statement, as a hypothesis, gives the Lean statement
  on the Lean's instances, by the transfer test (§7.1) or closed-list steps.
- Labels: both directions → `Same`, whatever the axes propose; forward only → `Wider` (`strict:
  unknown` unless a reason the converse fails is named); reverse only → `Narrower`; neither →
  `Mixed`, or `None` under K5/K6. A matrix label the evidence does not certify is replaced by the
  certified one.

**Checker.** The migration makes `check_coverage_audit.py` compute scope and coverage from the
recorded axes and fail a hand-written cell that disagrees; it accepts `None` and `Refuted`.

**Headline** (author, 2026-11-22: total `Yes`, with the split beside it). Coverage `Yes` is
reported in four columns: **proved** (theorem rows whose every component is proved), **argued**
(§7.9), **stated** (roles definition, conjecture and assumption, whose `Yes` certifies a faithful
statement, not a proof), and **provisional** (rows flagged `missing_context` or
`aggregation_sensitive`, until resolved). The headline quotes the total `Yes` with the four counts
beside it.

**Below print** = Narrower, Mixed, None or Refuted. Each below-print row is owed work under the
standing rule (§9). A row whose cited declarations prove nothing of print (B = none) stays a graded
row, below print (author, 2026-11-22); a row with no atlas statement at all is coverage `No`, scope
`—`, ungraded and not owed.

## 7. Special cases

7.1 **Representation.** Notation, names, `Fin n` for {1..n}, curried versus uncurried, bundled
versus unbundled, an exposed implicit parameter, and any generalization that passes the **transfer
test**: (i) every print instance is a Lean instance (after C's translation), and (ii) named transfer
lemmas give a map φ from Lean instances to print instances with `LeanHyp x → PrintHyp (φ x)` and
`PrintConcl (φ x) → LeanConcl x`, so that the Lean statement follows from the printed one **through
print's conclusion**. A lemma that reaches the Lean conclusion without a `PrintConcl` premise (an
independent proof of the general case) is not a transfer. Then the two statements are equivalent and
the difference has no effect on any axis. If no such φ is named, the difference broadens with
`strict: unknown` (the grader records "transfer not found", not "no transfer exists"). Example: an arbitrary
probability space with finite-range random variables, where every quantity depends only on the joint
law, transfers through the pushforward pmf (E27). A map that preserves truth values is not enough:
for a proved theorem every map does (E2). An inclusion that misses some print instances fails (i)
and is graded on A (E38).

7.2 **Definitions.** C compares the defined object; A compares the accepted inputs (input loss
narrows); B is `same` if the defining conditions agree on the inputs both accept, otherwise
`incomparable` (Mixed): a stronger or weaker defining predicate defines a different object, and the
old "Same with a note" is retired. Inequivalent readings of print's definition: §7.6.

7.3 **Several declarations.** For each print component, list the routes (cited declarations) that
establish it; the component is covered on the **union** of their instance sets, each route counting
only once its specialization to print is checked (C0a, A7). The row is covered where **every**
component is covered (intersection over components of the unions over routes). Components sharing a
universally bound variable (the same game, the same agent) combine pointwise across routes (E34).
Components sharing an **existential witness** are covered only where the cited declarations,
combined by closed-list steps, give one witness meeting all the shared clauses; routes that prove
the clauses with possibly different witnesses establish only the weaker projections (E37). With more than two routes, state
the split of print's instances explicitly. If the result cannot be stated as one A/B pair, record
the pair of the intersection (the instances on which every component is covered), give a per-route
account and set `aggregation_sensitive: true`.

7.4 **Missing context.** Follow the conservative default the rule names (narrowing, proxy, missing),
set `missing_context: true`, and say what is needed.

7.5 **Roles.** The role follows from print's own words, by these tests, in this order: `no-print` if
no printed statement exists (a row with a printed statement is never `no-print`); `conjecture` if
print calls it a conjecture, open problem or question, or says it is unproved; `theorem` if print
asserts anything beyond a definition (a text that defines and asserts, "we call f optimal if ...;
such f exists", is a theorem); `definition` if print only defines ("we define", "we call", "let ...
denote"); `assumption` if print asks the reader to assume a standing condition outside any theorem;
`explanatory` if print asserts nothing precise. A role the grader cannot fix by these tests is `theorem` and is flagged
`interpretation_sensitive`.
- `theorem`: an assertion (theorem, lemma, proposition, corollary, a claim in a remark).
- `definition`: §7.2.
- `assumption`: print asks the reader to assume a condition. C compares its objects; A the domain
  on which it is stated; B is `same` when a Lean hypothesis or predicate states the condition where
  the source uses it (fidelity, not a proof). A clause restricting a parameter's domain is graded on
  A only.
- `conjecture` (ruling R15): an open problem or conjecture print states without proof. Graded by its
  Prop rendering at print's quantifiers, as a definition of the claim: C and A as usual, B `same`
  when the Prop is print's. Coverage `Yes` certifies the statement (headline column **stated**); a
  separate field `proof: open | proved` records its status. A conjecture refuted in Lean goes to
  §7.7. A conjecture used as a premise of another claim is A1/E11 there.
- `explanatory`: motivation with no precise claim. State the claim you read, warrant it from the
  text (§7.6), and set `interpretation_sensitive: true` unless a ruling fixes the reading.
- `no-print`: a result the Atlas proves that no printed statement states. Scope `Beyond`,
  coverage `—`, outside the graded count.
- A notational convention is representation (§7.1).

7.6 **Several readings.** If readings consistent with the packet and page give different labels and
no ruling settles them: grade the **conservative** reading, the lowest in the order
Refuted < None < Mixed < Narrower < Same < Wider; record each other reading and the label it gives,
and set `interpretation_sensitive: true`. A reading under which print is refuted makes the row
`needs-ruling` (§9) and is graded Refuted until the author rules. Applies to informal premises,
objects, quantifier order, defining conditions and conclusions alike. The grade then moves by a
ruling, with its sweep, or by another trigger of §10.
A row this rule moves below print is listed for the author as a reading question, with the grade
under each answer (author, 2026-11-22).

Explanatory prose stays a graded row (author, 2026-11-22) once the claim read from it is written out
and warranted (§7.5).

7.7 **Refuted print and repairs.**
- **Refutation evidence** is a Lean declaration (a refutation file under
  `docs/provenance/refutations/` or a library theorem) proving the negation of the literal statement,
  or proving that a countermodel meets every hypothesis of print (all four kinds) and violates its
  conclusion. A countermodel checked only by hand or script is a lead, not evidence; one that drops a
  scoping clause is neither.
- **Unrepaired**: scope `Refuted`, coverage `No`; the row records the evidence.
- **Repair**: the author accepts a repair when the literal print is proved wrong and the repair is
  necessary and minimal (it changes only what the refutation forces and keeps the surrounding text's
  evident intent). The row is then graded against the repaired print, records `repair: <ruling id>`
  and `refutation: <file>`, and is counted once, under the repaired grade, flagged `repaired`.
- **Partial refutation**: when one component is refuted and a repair is accepted, the repaired
  component is graded against the repair and the others as printed. Without an accepted repair the
  row is `Refuted` (coverage `No`), its other components recorded in the defect record, and the row
  is `needs-ruling`.

7.8 **Citation gaps.** If a declaration at HEAD carries part of the row and is not cited, record
the gap and the counterfactual grade on the cited set alone; the audit grade is taken after the
citation is added. An upgrade stands only if a declaration at HEAD, cited or citable, carries it.

7.9 **Argued steps.** A step off §0's closed list, on any axis (a C correspondence, an A
implication, a B component), is `argued` when it (i) cites a published theorem or a standard identity
by name, (ii) checks that theorem's hypotheses at this use, each named (integrability for Fubini,
for example), and (iii) is not the row's own claim or the main argument print gives for it. A step
failing (i)-(iii) is not argued: it counts as not shown (C `proxy`, A `narrower`, B `missing`). An
An A implication that is not shown leaves the difference standing (an added hypothesis narrows). An
argued row is graded as if proved, flagged `argued: true` per component, reported in the headline's
**argued** column (§6), and carries a defect record for the owed Lean proof even when its scope is
Same or Wider (§9).

## 8. Rulings with general force

The register (`docs/provenance/regrade-2026-11/RULINGS-PENDING.md` and `ADJUDICATION-LOG.md` beside it) holds every
ruling. These have general force and apply to every row:

- G1. **Standing interpretations.** Rulings are part of print's meaning, applied like a definition in
  the source; never evidence about the Lean.
- G2. **Repairs** on the conditions of §7.7.
- G3. **Attainment presupposition** (R3 and its extension): a printed argmax, "takes the action with
  the highest value", or max over a class, used as a maximiser, presupposes that the maximum is
  attained; an attainment hypothesis renders print. An explicit attainment claim still needs proof.
- G4. **Conjectures** (R15): §7.5.
- G5. **Downgrade witnesses** meet every hypothesis of print, the standing assumptions, every ruling
  and every accepted repair.
- G6. **Own row only.** A clause counts against a row only if it is part of that row's printed
  statement; a neighbouring sentence graded in its own row is not owed here.
- G7. **Existential reading** (row 018): print's "can" or "can lead to" is existential by default;
  one inhabited instance meeting B4 carries it. The default yields where print's context fixes another
  reading, quoted (for example 287's "can be reduced to a half (but not lower)": attainment plus a
  bound).
- G8. **Conservative default** for readings no ruling settles (§7.6).
- G9. **Sweep.** Every ruling is followed by a sweep of the rows it could decide, recorded with it.
- G10. **Definedness presupposition** (author, 2026-11-22; generalizes R3, R6, R9 and the 2.10.1
  ruling): a hypothesis needed for a printed expression to be defined (a maximum attained where print
  uses the maximiser, a sum or expectation that exists, a program set on which print's weights sum,
  a logarithm's argument positive) renders print. The grader quotes the printed expression and shows
  the hypothesis is necessary for it to be defined (not merely convenient, as integrability for a
  bound print states about a defined quantity would be). **Bound:** it never turns a claim print
  makes into a free hypothesis; where print asserts the property (for example "the maximum is
  attained"), it is a component owed a proof.

- G11. **Transfers checked by hand count** (author, 2026-11-22): a §7.1 transfer derived by
  closed-list steps through print's conclusion certifies the reverse direction without a Lean
  declaration; the row records that the transfer is hand-derived, and a Lean lemma replaces it when
  one is written.
- G12. **Definitions** (author, 2026-11-22): the §7.1 transfer test applies to a definition's accepted
  inputs; a definition accepting more inputs, whose defining condition is print's pulled back along
  one map, is `Same`.
- G13. **One map** (author, 2026-11-22): §7.1 asks for a single map φ; a family of maps, one per
  sub-instance, does not certify the reverse direction.

Every other ruling is a reading of one source and lives in the register with that source.

## 9. Owed work: the standing rule and remedies

**Scope ≥ print wherever achievable.** Each below-print row carries one **defect record** per
below-print axis, and each argued step carries one whatever the row's scope: axis; kind; print quote and page; Lean declaration, file:line and binder; the
violating print instance (A) or failing component (B) or uncorresponded object (C); state; remedy.

States: `closed` (discharged; regrade), `unclosable` (with the witness that proves it), `costed`
(S < 50 lines, M < 300, L more), `needs-ruling` (a reading decides it; name the question).

| Label | Remedy |
|---|---|
| C proxy | build print's object, or prove the correspondence (C becomes `equivalent`) |
| A narrower or incomparable | for each narrowing difference: prove the hypothesis from print's, drop it, instantiate the interface for print's object (A7), add a route for the excluded instances (§7.3), or refute the wider statement and record it unclosable |
| B weaker or incomparable | prove the missing component or direction, tighten the bound, swap the quantifiers; for a proxy, go to C |
| B none | build the first result that renders print, or prove the defect `unclosable`; the row stays owed meanwhile (author, 2026-11-22); to stop claiming a rendering, remove the citations, which makes the row an ungraded `No` |
| Refuted | ask for a repair ruling (§7.7) |
| argued | prove the off-list step in Lean |

## 10. Change rule (replaces "Stability")

A row's grade changes only on: (a) new Lean, or a change to its citation set; (b) new source
evidence (a page, an erratum, a published version); (c) a recorded ruling, with its sweep; (d) a
change of this specification's version, with a published mapping from the old labels and the
regrade's provenance. A re-reading of a text already read, without one of these, does not move a
row. Contested grades name the rendered page that settles them.

## 11. What the audit table records per row

Role; C, A, B; computed scope and coverage; flags (`repaired`, `refutes`, `argued`,
`interpretation_sensitive`, `missing_context`, `aggregation_sensitive`, `leaner`); rulings applied;
open questions; decided-by (provenance pointer); and for a below-print row its defect records (§9).
The registry's relationship labels (EXACT, EQUIVALENT, RELATED) are independent of scope and are not
changed by this specification.

## 12. Calibration examples (synthetic)

| # | Print | Lean | C | A | B | Scope |
|---|---|---|---|---|---|---|
| E1 | For finite X, \|P(X)\| = 2^\|X\| | For any Fintype α, card (Set α) = 2^card α | own | same (representation) | same | Same |
| E2 | f:[0,1]→ℝ continuous attains a max | f:K→ℝ continuous, K compact nonempty | own | broader (A6: no transfer from the [0,1] statement to a Cantor-set K by closed-list steps; witness K = Cantor set) | same | Wider |
| E3 | For n ≥ 1, a_n ≤ 2/n | For n ≥ 1, a_n ≤ 1/n | own | same | stronger | Wider |
| E4 | V* = sup over policies of the infinite-horizon value satisfies Bellman | depth-n V_n satisfies the depth-n recursion; no V_n → V* lemma | proxy (C0b) | same | none (B1, K6) | None |
| E5 | as E4 | Lean defines V∞ := lim V_n, proves V∞ = sup over policies of the infinite-horizon value, and Bellman for V∞ | equivalent (V∞ bridged to print's V* by the named lemma) | same | same | Same |
| E6 | If X ⊥ Y given Z then I(X;Y\|Z)=0 and I(X;Y) ≤ H(Z) | only I(X;Y\|Z)=0 | own | same | weaker | Narrower |
| E7 | For every agent π, P(π) | for every agent with bounded rewards, P(π) | own | narrower | same | Narrower |
| E8 | For every agent π, P(π) | bounded rewards, P'(π) with P' ⇒ P | own | narrower | stronger | Mixed |
| E9 | Agent A* satisfies β | every agent meeting H1-H4 satisfies β; H1-H4 never proved for A* | own (C0a) | incomparable (generality broadens: witness another agent meeting H1-H4; unproved H1-H4 narrow, A11) | same | Mixed, `conditional` |
| E10 | Under Conjecture K, S | S assuming K | own | same | same | Same |
| E11 | S (no conjecture) | S assuming K | own | narrower (A1, A11) | same | Narrower, `conditional` (reverse entailment: S implies K → S) |
| E12 | ∀x ∃y R | ∃y ∀x R | own | same | stronger | Wider |
| E13 | finite X with \|X\| = n ≥ 1, P(X) | "finite" dropped (implied) | own | same, leaner | same | Same |
| E14 | finite group of odd order, P(G) | any finite group, P(G) | own | broader | same | Wider |
| E15 | effectivity function on a finite player set | any player type | own | broader (A6) | same | Wider |
| E16 | "if the human's policy is suboptimal, assistance has positive value" | hypothesis `value noop < optValue`, conclusion the positive value | own | same (the hypothesis renders print's antecedent "suboptimal", quoted; never a printed consequent) | same | Same |
| E17 | silent on finiteness; Setting: "variables take finitely many values" | `Fintype` on variables | own | same (standing assumption) | same | Same |
| E18 | condition (ii) holds for every effectivity function | proved only for those of a surjective game form | own (C0) | narrower | same | Narrower |
| E19 | finite X, probability measure μ: μ(A ∩ B) ≤ μ(A) | finite X, any finite measure (zero allowed) | own | same (§7.1: φ(μ) = μ/μ(X), with `PrintConcl (φ μ) → LeanConcl μ` by scaling; the zero measure is degenerate) | same | Same |
| E20 | H(X\|Y) ≤ H(X) | same, with equality iff X ⊥ Y | own | same | stronger (B2) | Wider |
| E21 | finite X, property P | any X, `Fintype` added on Y (print unrestricted) | own | incomparable | same | Mixed |
| E22 | For the description complexity K, P(K) | for every `c : Complexity`, P(c); K meets both axioms by a named lemma | own (C0a) | broader (A6: witness c = a constant cost; no transfer from P(K) to P(c); A7 met) | same | Wider |
| E23 | as E22 | as E22, but K violates an axiom on some print instance | own | incomparable (generality broadens; that instance excluded) | same | Mixed |
| E24 | "assume the reward is bounded by M" | hypothesis `hbound` among others | own | same | same (assumption) | Same |
| E25 | some MDP makes policy iteration exponential | a specific chain family, proved exponential | own | same (B4) | same | Same |
| E26 | X for every finite game | Thm 1 for ≤ 2 players, Thm 2 for ≥ 2 players | own | same (§7.3 union) | same | Same |
| E27 | for random variables on a finite sample space, H(X,Y) ≤ H(X) + H(Y) | any probability space, X and Y of finite range | own | same (§7.1: pushforward to the joint pmf is claim-preserving) | same | Same |
| E28 | some finite graph has property P | some graph (possibly infinite) has P | own | same | weaker (A10/B4: witness outside print's class) | Narrower |
| E29 | for every structure meeting axioms α and β, Q | interface with fields α, β; each field extendable separately, never both at once for some print instance | own | narrower (A7, that instance) | same | Narrower |
| E30 | ∀ n, P n ∨ n = 0 | ∀ n > 0, P n | own | same (A12: at n = 0 print's conclusion holds trivially; forward certified by recovery, reverse by specialization) | same | Same |
| E31 | literal "reduced to a half" refuted in Lean; repair accepted | proves the repaired bound and its attainment | own | same | same | Same, `repaired` |
| E32 | Conjecture: every X has P | `def Conj : Prop := ∀ X, P X`, unproved | own | same | same (role conjecture) | Same, `proof: open` |
| E33 | under a reward-bounded MDP, P | P for a truncated reward standing for print's reward in the hypothesis | proxy (C3) | incomparable | same | Mixed |
| E34 | X for every finite game (two components sharing the game) | Thm 1 gives component 1 for all games; Thm 2 gives component 2 for ≤ 2 players only | own | narrower (§7.3: the row is covered where both components are, ≤ 2 players; A9) | same | Narrower |
| E35 | statement with a step "by Fubini" not in Lean | as print, Fubini step argued | own | same | same, `argued` | Same, flagged |
| E36 | literal print refuted, no repair ruled | Lean-checked countermodel at a print instance | — | — | — | Refuted |
| E37 | for every game G there is a strategy s with R(G, s) and T(G, s) | Thm 1: ∃ s, R(G, s); Thm 2: ∃ s, T(G, s) (possibly different s) | own | same | weaker (§7.3: shared witness s needs one route covering both) | Narrower |
| E38 | ∀ n : ℕ, P n | ∀ n > 0, P n; P 0 not recovered | own | narrower (§7.1 (i) fails: n = 0 is a print instance outside the Lean's; A12 does not apply) | same | Narrower |
| E39 | for every finite group G, P(G) | for every finite group G of order 0, P(G) | own | narrower | none (K5: no finite group has order 0) | None |
| E40 | ∀ n, P n | ∀ n > 0, P n ∧ P 0 | own | same | same (certification: both directions shown; B2's extra is already implied) | Same |

## 13. Output per row

```
{"id": "NNN", "role": "theorem|definition|assumption|conjecture|explanatory|no-print",
 "refutes": false, "repair": null, "refutation": null, "objects": "own|equivalent|proxy",
 "applicability": "broader|same|narrower|incomparable", "conclusion": "stronger|same|weaker|incomparable|none",
 "reason_C": "...", "reason_A": "... each difference, its effect, and A4/A5 witnesses",
 "reason_B": "... each component and its label", "readings": [{"reading": "...", "label": "..."}],
 "strict": "shown|unknown", "forward": "lift and transfer evidence, or empty",
 "reverse": "transfer or closed-list evidence, or empty", "conditional": false,
 "proof": null, "argued": false, "leaner": false,
 "missing_context": false, "interpretation_sensitive": false, "aggregation_sensitive": false,
 "citation_gap": "", "rulings_applied": [], "open_questions": [], "decided_by": "",
 "defects": [{"axis": "C|A|B|argued|refuted", "kind": "...", "print": "quote, page",
   "lean": "declaration, file:line, binder", "instance": "...", "state": "closed|unclosable|costed|needs-ruling",
   "cost": "S|M|L", "remedy": "..."}],
 "confidence": 1-5}
```

If `refutes` is true and no repair is accepted, set the axes to null. `proof` is set only for role
`conjecture`.
