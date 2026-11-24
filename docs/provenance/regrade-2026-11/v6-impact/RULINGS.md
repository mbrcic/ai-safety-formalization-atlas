# Author rulings and accepted repairs (apply as print's meaning)

These are standing interpretations of print, applied exactly like a definition in the source. They are not evidence about the Lean.

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

- **R5** (author, 2026-11-21, round 2): Ring–Orseau Statements 1 and 3 are graded under footnote 5
  ("P(DB) as high as needed"); the step ρ(q_b) < ρ(Q_B) ⇒ P(DB) > 1/2 is not owed. Readings confirmed:
  row 160's convergence sentence is a hedged expectation (not graded); row 240's "mistakes tend to
  zero" is per step; row 090's P(v_i | pa_i) is one fixed mechanism table. Still open: R13, R14(a),
  whether infinite-entropy variables are in scope for Cover–Thomas 2.10.1, the window completion for
  row 087 (window indicator or any horizon equal to 1 on the window), "episodic" for row 193, and the

- **Window completion** (Ring–Orseau A_rl; rows 087, 131): the horizon is the window indicator,
  w(t,k) = 1 if k − t ≤ m and 0 otherwise (as the companion paper prints for this agent).
- **Appendix A, Proposition 10** (Armstrong–Mindermann; row 286): "If L is reasonable" includes the
  length and running-time overhead assumptions of the proof sketch (application, zero-reward
  algorithm, hard-wiring, wrappers); the `TimedLanguage` / `Wrapping` overhead fields are print's.
- **Cover–Thomas 2.10.1** (row 314): infinite-entropy variables are out of scope (print's
  real-valued identities); a finite-entropy hypothesis on X is print's.
- Still open: R13 (row 135).


- **R3 extended**: a printed max over a class (Everitt Def. 10's max over environments μ ∈ M and
  over π̌) presupposes attainment, as R3 does for argmax; a class where the max is not attained is
  not an instance of print (row 289; also 042).
- **Neighbouring sentence, row 064**: App. A.2's invariance sentence ("positive affine
  transformation ... set of optimal policies invariant ... re-scale regret bounds") belongs to the
  separate audit row "App. A.2, invariance of the optimum under eq. (2)", not to 064.
- **Row 206**: graded under print's one-planner reading (p(R) = π̇′ for one planner across all
  agent actions).
- **Armstrong–Mindermann p_g tie rule** (016, 048, 174, 274; exposed 021, 059, 106, 111, 152, 153,
  197, 235, 239, 286): not ruled; closed in Lean by renderings over an arbitrary greedy planner
  (any g with g(R)(s) a maximiser of R(s,·)) — wave 6.
- **Row 215**: not ruled; closed in Lean by Example 1 (two frames, equal alpha powers, different
  actual powers) — wave 6.
- Still open: R13 (row 135).


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

- Still open: R13 (row 135); R11 (Pearl "discrete": rows 205, 293 since round 3b; it had left the later lists only because row 090 stopped depending on it).


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


- **Row 018, Manheim-Garrabrant extremal Goodhart, "so that the relationship collapses"**: print's
  "model insufficiency can lead to extremal Goodhart" is existential: "this can happen". One inhabited
  instance of all three clauses (fit on the region, selection leaving it, collapse at the actual goal)
  carries the claim. The universal reading (fit plus escape always gives collapse) is not print's; it
  is false in any case.


- A row whose cited declarations prove nothing of print (B = none) stays graded, below print, owed.
- A reading no ruling settles is graded conservatively; each row this moves below print comes to the
  author as a reading question with the grade under each answer.
- Explanatory prose stays a graded row once the claim read from it is stated and warranted.
- Definedness presupposition (G10), general and bounded: a hypothesis needed for a printed expression
  to be defined renders print; it never turns a claim print makes into a free hypothesis.


## Further accepted repairs (grade against the repaired print)

- Accepted repairs (author rulings 2026-11-14, 2026-11-20 and 2026-11-21; grade these rows against
  the repaired print; each literal print is refuted in Lean in `docs/provenance/refutations/`):
  S03-R08 Ashby 11/9 (`ashby-11-9-literal.lean`); 228 and 271 Peleg Ex. 2.3/3.6
  (`peleg-ex-2-3-literal.lean`); 246 Peleg Thm 3.5 (`peleg-thm-3-5-literal.lean`); 172 Skalse
  footnote 5, R1 non-trivial (`skalse-footnote-5-literal.lean`); 035 Pauly Thm 3.2 at finite outcome
  sets (`pauly-thm-3-2-literal.lean`); 046 Everitt Thm 11, observed histories
  (`everitt-thm-11-literal.lean`); 305 Ashby 11/7 (`ashby-11-7-literal.lean`); 180 Lemma B.7
  (`eu-lemma-b7-literal.lean`); 224 Rice, non-trivial extensional property (`rice-literal.lean`); 201
  Cover-Thomas 2.8.1, 'only if' at finite I(X;Y) (`cover-thomas-2-8-1-literal.lean`); and 183, 025,
  091, 198 as listed in `ADJUDICATION-LOG.md`. A downgrade may not rest on the literal print
  of these rows; attack the repaired print, or argue in `notes` that the repair is not necessary and
  minimal (and still grade against it).
