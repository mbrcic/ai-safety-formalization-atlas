> The adjudication briefs and author rulings of the 2026-11 regrade, in order (formerly
> `adjudication-full-v5/BRIEF-ruling-adjudication.md`). The briefs are quoted as given; the
> intermediate grading files they name are not published. Final grades: `final-grades.tsv`.

# Adjudication under the author's rulings of 2026-11-21

Follow BRIEF-fix-adjudication.md in this folder (which builds on BRIEF.md), with N your part number
(part<N>.tsv, output ruladj<N>.jsonl), and these changes.

The author has ruled on how to read print. These rulings are now part of print's meaning: apply them
as standing interpretations, exactly as you would a definition in the source. They are not evidence
about the Lean; check the Lean as usual.

- **R1**: Ring–Orseau's "it must be summable: Σ_{k=t}^∞ w(t,k) < ∞" means absolute summability; a
  Lean hypothesis `Summable |w|` (or `Summable (fun k ↦ |w t k|)`) renders print's own condition (no
  effect). Signed, conditionally summable horizons are not print instances.
- **R2**: Ring–Orseau's v_t is the limit of the finite-depth values with zero continuation (the series
  value), not any solution of the recursion (1)-(2); `infiniteValue := limUnder (value n)` is print's
  object (own), and lemmas tying it to the recursion are bonus, not owed.
- **R8**: at an infinite vertex set, "directed acyclic graph" / "given by recursive application of the
  structural functions" means a well-founded parent relation; `IsWellFounded` renders print (no effect).
- **R9**: print's utility sum U := Σ_{U∈𝐔} U ranges over finitely many utility vertices; Definition 17's
  SCIMs have finitely many vertices; max_π ranges over all policies and print presupposes E_π exists for
  each (so an all-policies measurability hypothesis has no effect). Finite-utility, finite-vertex and
  all-policies-measurable hypotheses are print's (no effect).
- **Repairs accepted** (grade against the repaired print; the literal print is refuted, or being
  refuted, in docs/provenance/refutations/):
  - 183 (S03-R05, Ashby §11/8): the last display reads H(E) ≥ H(D) + H_D(R) − H(R).
  - 025 (S19-R12, Breuer): "properly included ⇒ strictly more states" is read inside the finite remark
    (finite O).
  - 091 (S17-R04, Manheim–Garrabrant): claim (3) is about the Simple Model of eq. (1) (proxy = goal +
    independent noise); claim (2) holds for a non-degenerate (non-point-mass) goal.
  - 198 (S03-R07, Ashby §11/8): "H(E)'s minimum is H(D) − H(R)" is attained over arbitrary E meeting
    print's premise (not necessarily a table outcome).
- Questions the author has NOT ruled on (e.g. whether the maximum is attained, footnote 5's threshold, Def. 17's quantifier order, the judge reading of
  Melo et al.) stay open: grade them as before (conservative default) and say which open question, if
  any, keeps the row below print.
- Read binders as elaborated: an `omit ... in` line above a declaration removes that ambient instance.
- Output fields as in BRIEF.md, plus "rulings_applied": [the R-numbers or "repair" that changed
  anything] and "open_questions": [unruled questions that still affect the grade].

## Parts 66 and 67 (rows not yet re-adjudicated under the rulings)

- Also standing: the author's repair of 2026-11-20 for row 201 (S01-R06, Cover–Thomas 2.8.1): the
  equality clause's "only if" is restricted to finite I(X;Y) (`docs/provenance/refutations/
  cover-thomas-2-8-1-literal.lean`); grade 201 against that repaired print.
- Grade against the Lean at HEAD, not only the declarations the packet or audit cites: if a
  declaration at HEAD closes a defect, name it (full name, file:line) and grade with it, and record
  the citation gap in `reason` (as in ruladj65.jsonl), with the counterfactual grade on the cited
  declarations alone.
- Still open (not ruled): R10 (Def. 17 quantifier order), R11 (Pearl "discrete"), and the others in
  RULINGS-PENDING.md. Decide them as print reads, conservatively where print is genuinely open, and
  name in `open_questions` any that keep the row below print.

## Further rulings (author, 2026-11-21, later): standing interpretations, apply like the ones above

- **R3**: argmax / "takes the action with the highest value" presupposes attainment; a hypothesis
  that the maximum is attained is print's (no effect). An action set with no maximiser is not an
  instance of print.
- **R4**: footnote 4's lexicographic tie-break needs only a least maximiser at each tie, not a
  well-founded order; a well-foundedness hypothesis on the action order narrows; the least-maximiser
  route (`lexArgmaxOfLeast`, `InfLexAttains`) is print's own.
- **R6**: AIXI's program set Q is that of a prefix universal machine; a summability / uniquely-decodable
  hypothesis on Q is print's (no effect).
- **R10**: Definition 17 (2): d is chosen after π* (∀π* ∃d); `HasICIAt` is print's.
- **R12**: Melo et al.'s P is total correctness (every input gets an accepted output; `judgeSpec`).
- **R15**: an open conjecture row is graded by its Prop rendering at print's quantifier (no proof owed).
- **R16**: Armstrong–Mindermann planner complexity is read with exact (rational) reward tables
  (coding (a)).
- **R17**: for 198's repaired minimum, the attaining E may live on an extension carrying a copy of
  (D, R) with the same joint law.
Still open: R5, R11, R13, R14(a).

## Round-2 rulings and parts 71-72 (fix wave 5)

- **R5** (author, 2026-11-21, round 2): Ring–Orseau Statements 1 and 3 are graded under footnote 5
  ("P(DB) as high as needed"); the step ρ(q_b) < ρ(Q_B) ⇒ P(DB) > 1/2 is not owed. Readings confirmed:
  row 160's convergence sentence is a hedged expectation (not graded); row 240's "mistakes tend to
  zero" is per step; row 090's P(v_i | pa_i) is one fixed mechanism table. Still open: R13, R14(a),
  whether infinite-entropy variables are in scope for Cover–Thomas 2.10.1, the window completion for
  row 087 (window indicator or any horizon equal to 1 on the window), "episodic" for row 193, and the
  hybrid reward coding for row 021 (beyond R16 (a)'s wording).
- Parts 71 and 72 regrade the rows of fix wave 5 (`BRIEF-lean-fixes-w5.md`, logs
  `lean-fixes-*5.jsonl`). The Lean is the working tree on disk (read files directly). The blind
  wave-5 grades are in `grading/fix-w5/{claude,claude-pass2,codex,grok}/` (those graders did not
  know the rulings); read their reasons and check each objection against print and HEAD: say for each
  NM objection whether a ruling removes it, the Lean answers it, or it stands.
- The rules of "Parts 66 and 67" apply (grade the Lean at HEAD, record citation gaps and the
  counterfactual).

## Rulings of 2026-11-21, round 3 (author: "do as recommended")

- **Window completion** (Ring–Orseau A_rl; rows 087, 131): the horizon is the window indicator,
  w(t,k) = 1 if k − t ≤ m and 0 otherwise (as the companion paper prints for this agent).
- **Appendix A, Proposition 10** (Armstrong–Mindermann; row 286): "If L is reasonable" includes the
  length and running-time overhead assumptions of the proof sketch (application, zero-reward
  algorithm, hard-wiring, wrappers); the `TimedLanguage` / `Wrapping` overhead fields are print's.
- **Cover–Thomas 2.10.1** (row 314): infinite-entropy variables are out of scope (print's
  real-valued identities); a finite-entropy hypothesis on X is print's.
- Still open: R13 (row 135).

## Part 74 (fix wave 5b)

Rows 240 and 207 after the wave-5b Lean (`lean-fixes-wh25.jsonl`: generated-run uniqueness for
footnote 6; the action-aware prediction agent `predictionAgentAct` and Statement 3 for print's argmax
predictor). Blind grades: `grading/fix-w5b/`. The earlier re-adjudications (ruladj71 id 207, ruladj72
id 240) named the defects these closures target; check whether each is closed. All rulings above
apply, including the round-3 window indicator.

## Parts 75-77 (adversarial round 3: disputed grades)

Round 3 (`ADVERSARIAL-ROUND3.md`) attacked 159 Same/Wider grades. Rows where referees disagree on a
downgrade (2 of 3 downgrade, or 1-1 between two referees, or a lone referee), and rows where 2 or 3
referees propose an upgrade, come here. Each referee line for your rows is in `adv3-referees.jsonl`
(field `id`; verdict, scope_found, axis, print_quote, page, lean, mapping, witness, notes). This is a
cross-examination: read every referee line for the row, both sides, and decide on the page and the
Lean at HEAD (working tree). You may read the earlier adjudications of the row.
- A downgrade stands only if its witness meets every hypothesis of print, the standing assumptions of
  the source, every ruling above and the accepted repairs (listed in `ADVERSARIAL-ROUND3.md`,
  Inputs); or if the proxy difference is real at a print instance. A witness that drops a scoping
  clause of print (e.g. a non-summable horizon, against R1) fails.
- A claimed print clause with no Lean counterpart counts only if it is part of this row's printed
  statement (packet part (a)), not a neighbouring row's; say which.
- An upgrade stands only if a declaration at HEAD, cited or citable, carries it; if it is not cited
  in the audit row, set "citation_gap": "<declaration names>".
- Where the decision rests on a reading no ruling settles, grade under the conservative default and
  name the question in `open_questions`, with the grade under the other reading in `notes`.
- Output: as above, plus "referees_upheld": ["codex"|"grok"|"opus", ...] (whose verdict you confirm),
  "citation_gap" (or empty), "notes".

## Rulings of 2026-11-22, after adversarial round 3 (author: "do as recommended")

- **R3 extended**: a printed max over a class (Everitt Def. 10's max over environments μ ∈ M and
  over π̌) presupposes attainment, as R3 does for argmax; a class where the max is not attained is
  not an instance of print (row 289; also 042).
- **Neighbouring sentence, row 064**: App. A.2's invariance sentence ("positive affine
  transformation ... set of optimal policies invariant ... re-scale regret bounds") belongs to the
  separate audit row "App. A.2, invariance of the optimum under eq. (2)", not to 064.
- **Row 206**: graded under print's one-planner reading (p(R) = π̇′ for one planner across all
  agent actions); the row is closed in Lean or stays Mixed.
- **Armstrong–Mindermann p_g tie rule** (016, 048, 174, 274; exposed 021, 059, 106, 111, 152, 153,
  197, 235, 239, 286): not ruled; closed in Lean by renderings over an arbitrary greedy planner
  (any g with g(R)(s) a maximiser of R(s,·)) — wave 6.
- **Row 215**: not ruled; closed in Lean by Example 1 (two frames, equal alpha powers, different
  actual powers) — wave 6.
- Still open: R13 (row 135).

## Part 78 (adversarial round 3, second referee pass)

As parts 75-77, with these additions. The referee lines in `adv3-referees.jsonl` now include a
fresh Opus referee (`"referee": "opus2"`, batches F01-F11) and, for E16-E18, Codex; read them all.
Rows come here because two or more referees propose an upgrade (014, 083), a second referee joins
a downgrade on a row adjudicated in parts 75-77 (065, 133: read that adjudication, last line in
`ruladj77.jsonl`, and decide whether the new referee's argument changes it), or the grounded Codex
cross-check disagrees with the part-77 adjudication (060: its line is in `adv3-crosscheck.jsonl`).
For 133, the wave-6 module `AISafetyAtlas/Preference/OverrideOnePlanner.lean` (start-dependent
regret `startRegret`, `OverridesFromStart`, bridge `OverrideModel.overridesFor_iff_overridesFromStart`)
is at HEAD; if it carries print where the cited set does not, record it as a citation gap.

## Parts 79-81 (fix wave 6, after adversarial round 3)

Rows whose Lean or citation changed in wave 6: new Lean (`lean-fixes-greedy6.jsonl`: every
Armstrong-Mindermann result at an arbitrary greedy planner; `lean-fixes-override6.jsonl`:
start-dependent regret, Definition 11 with one planner; `lean-fixes-sov6.jsonl`: Example 1 and
"actual powers are more precise than alpha powers") and the citation gaps confirmed in parts 75-78
or by round-3 referees (`fix6-cites.jsonl` lists what each row's citation cell gained). Packets were
rebuilt; blind grades are in `grading/fix-w6/` (Claude twice, Codex; no Grok). Decide each row on the
page and the Lean at HEAD under every ruling above (including 2026-11-22: R3 extended, 064, 206) and
the accepted repairs (`ADVERSARIAL-ROUND3.md`, Inputs: 172 and 228 are graded against the repaired
print; a blind grader's "refutes" on the literal print of a repaired row does not count). Read the
row's earlier adjudication (last line in `ruladj*.jsonl`, `fixadj*.jsonl`) and its round-3 referee
lines (`adv3-referees.jsonl`). The blind grades are evidence, not votes. Where a reading no ruling
settles decides the row, follow the "Parts 75-77" rule (conservative default, open_questions, the
other grade in notes). Output schema as ruladj78.

## Part 82 (row 153 after the infinite-complexity closure)

Part 79 graded 153 Mixed on an open question: whether print's comparable complexity covers pairs
with no description (K_L = ∞). The row now also cites `ComparableComplexityIn` (comparable complexity
at any ordered additive complexity, e.g. ENat), `comparableComplexityIn_iff` (the bridge to
`ComparableComplexity` at natural values) and `not_comparableComplexityIn_top` (a ⊤ pair is comparable
with no finite pair). Read part 79's line for 153 and decide the row as in parts 79-81.

## Rulings of 2026-11-22, later (author: "do as recommended")

- **Row 060, "accept the same language"** (Melo et al. p. 3): the same computed partial function
  (I/O map), as the Rice framing on that page reads it ("restatement of Rice's Theorem"; the next
  paragraph's "computes a partial function with property P"). Not the set of accepted (halting)
  inputs. The constant-0 / constant-1 witness refutes only the reading not adopted.
- **Row 286, code-planner compatibility** (Armstrong–Mindermann Prop. 10): a planner q that reads
  reward code is compatible with π̇ for R when every code of R makes q output π̇ (universal, as
  `CodeCompatible` states). The existential reading (some code) is not print's.
- **Row 286, radius**: "the results of Proposition 7 still apply" is amongst the lowest within a
  constant that depends on L and on the planner/wrapper code (the Lean's l(α_q) + 3c + log(1+c) and
  l(α_q) + 4c), as print's sketch itself carries l(α_p_g) and the wrapper overheads ("only slightly
  higher than that of π̇"); not Prop. 7's F-bound c alone.
- **p_g tie rule** (021; also the rows closed in wave 6 at an arbitrary greedy planner): p_g is
  footnote 9's fixed-order loop (`greedyOn`). Under an arbitrary maximiser selection print's claim
  (2) fails for 021 (some greedy planners have no description). Rows already closed at any greedy
  planner are unaffected.
- Sweep: the last adjudication lines that mention these readings (016, 028, 035, 048, 059, 065, 090,
  106, 109, 130, 131, 152, 160, 172, 174, 184, 215, 222, 227, 235, 274) are all Wider and do not
  depend on the reading not adopted (222: 060's question does not reach it, ruladj81). Only 060
  and 286 are re-adjudicated.
- Still open: R13 (row 135); R11 (Pearl "discrete": rows 205, 293 since round 3b; it had left the later lists only because row 090 stopped depending on it).

## Part 84 (rows 060 and 286 under the later 2026-11-22 rulings)

Read each row's last line (060: `ruladj80.jsonl`; 286: `ruladj79.jsonl`, and ruladj73 for the
universal-reading argument), its packet, the page, and the Lean at HEAD. Decide the row under every
ruling above, including the later 2026-11-22 rulings. The open questions those lines leave are now
ruled; any other unruled reading follows the "Parts 75-77" rule. Output schema as ruladj78.

## Parts 85-92 (round 3b: the 156 rows outside round 3's tiers)

Round 3b attacks the 156 Same/Wider rows round 3 did not reach (batches G01-G16, ADVERSARIAL-ROUND3.md
unchanged). Referees: a fresh Opus (`"referee": "opus3"`) on every row, Codex on G02-G10 (it did
not run on the rest), and a further fresh Opus (`"opus4"`) on the rows Codex did not reach and as
tiebreaker on single dissents (batches H01-H03). Rows come here when two referees agree on a
downgrade, or on an upgrade. Proceed exactly as "Parts 75-77" (cross-examination, every ruling above
including the later 2026-11-22 rulings, the accepted repairs, the conservative default, citation gaps
for upgrades carried only by uncited declarations). Most of these rows have no earlier adjudication:
their grade came from the blind panel majority (`grading/full-v5/`), which you may read. Output schema
as ruladj78, with "referees_upheld" drawn from "codex", "opus3", "opus4", "opus5" (the H04 tiebreaker).

## Rulings of 2026-11-22, wave 7 (author: "do as recommended")

- **Row 287, Ashby §11/6 "can be reduced to a half / a third (but not lower)"**: the repair is
  accepted, on the 2026-11-14 conditions (literal print proved wrong, repair necessary and minimal).
  Literal print is refuted in `docs/provenance/refutations/ashby-11-6-literal.lean`: at three
  disturbances and two moves every strategy on every column-injective table leaves at least two
  outcomes, never 3/2 (`not_literalPrint`, in the weaker "some table" reading), and the per-table
  reading fails without integrality at `T d r = d` (`diagonal_admits_all`). Repaired print: on every
  table with no repeat in a column every strategy leaves at least `|D|/c`, and at least `⌈|D|/c⌉`,
  outcomes; on some table of each shape some strategy leaves exactly `⌈|D|/c⌉` (`repaired_holds`).
  This is the §11/7 repair (row 305) one section earlier. Grade row 287 against the repaired print.
- Sweep for 287's ruling: the packets and last adjudication lines that mention §11/6 (029, 066, 086,
  141, 155, 198) either transcribe its context or cite its closing law ("only by further variety at
  R", 029), which the repair keeps; none rests on the attainment the repair drops. Only 287 changes.
- No other reading is ruled. R13 (row 135) stays open. R11 (Pearl "discrete") stays unruled; wave 7
  builds the countable-valued layer so that rows 205 and 293 no longer depend on it.

## Part 93 (Lean wave 7: rows 018, 050, 089, 188, 205, 249, 287, 293)

Wave 7 adds Lean for the rows round 3b left below print or graded on an argument not checked in Lean.
`lean-fixes-w7.jsonl` lists what was built for each row; the audit citation cells were extended
from `fix-w7-cites.jsonl` and the packets rebuilt. Read each row's last adjudication line, its
rebuilt packet, the page, and the Lean at HEAD (including the new declarations and their Examples
witnesses). Decide the row under every ruling above, including the wave-7 ruling on 287. Any other
unruled reading follows the "Parts 75-77" rule. Output schema as ruladj78, with "referees_upheld"
drawn from the blind wave-7 graders (`grading/fix-w7/`).

## Ruling of 2026-11-22, after the J01 recheck (author)

- **Row 018, Manheim-Garrabrant extremal Goodhart, "so that the relationship collapses"**: print's
  "model insufficiency can lead to extremal Goodhart" is existential: "this can happen". One inhabited
  instance of all three clauses (fit on the region, selection leaving it, collapse at the actual goal)
  carries the claim. The universal reading (fit plus escape always gives collapse) is not print's; it
  is false in any case. Grade unchanged (Same, `ruladj93`); the ruling removes the reading on which
  all three J01 referees and the Codex cross-check put 018 at confidence 2. "Collapses" occurs only in
  018 (round-3b sweep), so no other row depends on this ruling.

## Part 94 (grounded adjudication before release: 005, 135, 263)

The release would publish 005 and 135 as the only rows below print, and neither has a grounded
verdict: both are unanimous blind fix-wave regrades (`grading/fix-w4b/`). 263 is graded Wider by an
adjudication that recorded missing context (`fixadj37.jsonl`, last line for 263). Decide each row on
the printed page (render it; `pdftoppm -r 150`), the rebuilt packet (`grading/packets-v2/<id>.md`),
the audit row's citation cell, and the Lean at HEAD on disk (read binders as elaborated). Also read
the row's lines in `final.jsonl` (its `defects`), `redefects41-47.jsonl`, `defects*.jsonl` and the blind
grades for the id in `grading/fix-w4b/` and `grading/full-v5/`. Apply SPEC v5 and every ruling and
accepted repair above. R13 (row 135) is open: grade conservatively, name it, and give the grade under
each answer. For a row you grade below print, say whether the defect is closable in Lean, how (the
statement to prove), and its size (S < 50 lines, M < 300, L more), or give the witness that it is not.
Do not read `HANDOFF.md` or `STATS.md`. Output schema as ruladj78 (fields as in `ruladj93.jsonl`),
plus "referee" and "closure" (the closability verdict).

## Taxonomy rulings of 2026-11-22 (author, on SPEC v6; recorded in `spec/SPEC-v6.md`)

- A row whose cited declarations prove nothing of print (B = none) stays graded, below print, owed.
- A reading no ruling settles is graded conservatively; each row this moves below print comes to the
  author as a reading question with the grade under each answer.
- Explanatory prose stays a graded row once the claim read from it is stated and warranted.
- Definedness presupposition (G10), general and bounded: a hypothesis needed for a printed expression
  to be defined renders print; it never turns a claim print makes into a free hypothesis.
- Also applied as recommended (high confidence): carrier generalization is representation only
  when SPEC v6 §7.1's transfer test passes (every print instance is a Lean instance, and named lemmas
  give a map through print's conclusion); otherwise it broadens (A6). Argued components count in the
  headline with a flag (§7.9). R18 stays open. (This bullet first stated a truth-preserving-map test
  that the second-round reviews showed empty; superseded 2026-11-22.)
- (2026-11-22, author) Headline: total coverage Yes with the split beside it (proved, argued, stated,
  provisional; SPEC v6 §6). Impact pass: targeted, on the rows v6 can move.

## Part 95: the v6 impact pass (pre-registered 2026-11-22, before any v6 grade was seen)

Inputs frozen: SPEC v6 at commit 4b1d0399 plus the register fix of this commit (sha256 prefix
`4bf67c231af3fee6`); grader workspace `v6-impact/` (prompts, `RULINGS.md` scrubbed of grade outcomes,
batches; packets-v2 and a comment-free leantree at HEAD). Selection and tracks: `spec/MAPPING-to-v6.md`.

Decision rule:
1. A row's grade changes under v6 only if a grader or the adjudicator names the v6 rule that decides
   differently from v5 on this row (A6 transfer test, A10 polarity, A7 joint extension, A11/A12,
   B1/K5/K6, §6 certification, §7.2, §7.3 shared witness, §7.5 role, §7.9). A blind disagreement that
   names no v6 rule is re-reading noise (run-to-run flips are about 5-8%) and does not move the row
   (§10).
2. "Not shown" (forward certification, a transfer, a hypothesis implication) from a blind grader is
   not a witness (G5): such a row goes to grounded adjudication and never drops automatically.
3. Track F: if both blind graders agree with the current scope, the row holds. If either names a v6
   rule that moves it, or they disagree on the binary class, the row goes to grounded adjudication
   (fresh Fable; a Codex cross-check where the adjudication moves the binary class).
4. Track T: `transfer: found` from Codex is checked by a second grader (Fable); both found gives Same.
   Any row reported positive-existential, negative-position, `inclusion_fails` or `scope: below` moves
   to track F. Otherwise the row stays Wider, recorded with its A4 witness and `strict: unknown`.
5. A drop caused by an unruled reading (§7.6) comes to the author as a reading question with the grade
   under each answer; a certification failure confirmed by grounded adjudication is an ordinary regrade.
6. Control rows: if any of the 8 moves, widen the selection before migrating.
- Deviation (2026-11-22, during the pass): Codex stopped after F00-F07. Following the round-3
  precedent, a fresh Opus is the second blind grader on F08-F11 and the primary grader of track T
  (`referee: "opus"`), with Fable checking every `transfer: found`. Codex cross-checks of adjudications
  that move the binary class are deferred.

## Part 95 adjudication (grounded, v6 impact pass)

For each id in your list: the current grade is the row's line in `final.jsonl` (scope only) and its
last line across `ruladj*.jsonl` / `fixadj*.jsonl` / `out*.jsonl` (reasons). The blind v6 grades are the
row's lines in `v6-impact/out/{fable,codex,opus}_F*.jsonl` (track F) or `v6-impact/out/opus_T*.jsonl`
(track T: the transfer and polarity check; for a `transfer: found` line, decide whether the map passes
§7.1 through print's conclusion, which makes the row Same, and for an `other_concern` naming a
below-print problem, decide it). Decide the row under `spec/SPEC-v6.md`,
every ruling above and the accepted repairs, on the rendered page (`pdftoppm -r 150`), the packet
(`grading/packets-v2/<id>.md`) and the Lean at HEAD on disk (binders as elaborated). Apply Part 95's
decision rule: the grade changes from the current one only if you name the v6 rule that decides
differently from v5 on this row (`v6_rule`); "not shown" from a blind grader is a lead, never a
witness. For a downgrade give the witness or the unshown step and its cost; for a reading no ruling
settles, grade the conservative reading and give the grade under each reading (it will go to the
author). Do not read `HANDOFF.md` or `STATS.md`. Output per id one JSON line: SPEC v6 §13 fields plus
"scope", "current", "changes" (true/false), "v6_rule", "reading_question" (empty, or the question with
the grade under each answer), "referee".

## Author rulings of 2026-11-22 (v6 impact pass reading questions)

| Row | Ruling | Grade |
|---|---|---|
| 070 | Prove the lemma. `errorProb_mode_le_of_indepFun` (Fano.lean): a mode of `X` has error probability at most that of any guess independent of `X`, randomized included; cited | Wider (guess generalized to any constant) |
| 254 | (b): the definition sentence is about the Simple Model with independent noise (as for 018 and 091); five selection theorems cited | Wider |
| 259 | (a): no-print row (§7.5) | Beyond, coverage —, outside the graded count |
| 277 | (b): conditional on the Arguments' premises in their strong form; `program_ne_of_max` cited | Wider, flagged argued |
| 284 | (a): an assertion, closed by a composite carrier. `composite_restrict_surjective` (Embedded.lean): restriction `A × R → A` is onto for nonempty `R`, print's "O is composed of the apparatus A and of a rest R"; cited | Same |
| 115, 214, 195 | Pauly §3 / GJT Def. 2: `N` is any set ("more generally") | Same; siblings 031, 173, 232 read the same way |
| 156 | The class of worlds need not contain a non-actual world | Same |
| 230 | G7 covers "may be very different" | Wider |
| 314 | "Infinite-entropy variables are out of scope" restricts only `X` | Same |
| 299 | Print leaves field and time domain open | Same |

Still open: hand-derived transfers, transfer test for definitions, family transfers (288), the
mechanism-table reading for 148 and 090, R13, R18.

## Part 96: completion of the v6 impact pass (2026-11-23, Codex)

Codex adjudicated, in place of Fable (deviation). Brief as "Part 95 adjudication" above, plus: print from the second-read YAML transcriptions
(no page rendering), and the adjudications in `v6-impact/adjudication/A*`, `B*` and `OUTCOME.md` not
opened. Rows: the 34 not adjudicated in Part 95, 073 108 121 299 312, and cross-checks of 254 and 277.
Output `v6-impact/adjudication/C01`-`C07`. Blind Codex grades for F08-F11 and T00-T07 were restored
first. Lean transfers for the 22 hand-derived rows and for five track-T rows were written by Codex
and compiled (`docs/provenance/transfers/`, `v6-impact/transfers-lean.jsonl`); closures for 299
(done), 131 (failed, costed) and 207 (not attempted) in `v6-impact/closures.jsonl`.
Reading questions ruled 2026-11-23 (`RULINGS-PENDING.md`). Outcome: `v6-impact/OUTCOME.md`.
