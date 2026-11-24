# Author rulings pending (after fix wave 4b; rows listed are those still below print unless noted)

Source: the regrade's defect records (defects with `needs_ruling`; not published), the wave-3
adjudications and the Codex cross-check. 36 defect-level questions collapse to 15 readings, plus
overrides. Each line: the question, the rows it decides, what each answer does, the recommendation.
"Wider/Same" means the row (or that axis) stops counting below print; a repair needs a Lean refutation
of the literal print in `docs/provenance/refutations/` before it applies (2026-11-14 rule).

## Ruled 2026-11-14 and 2026-11-20 (author)

- **Only Lean-formalized statements count** (2026-11-14). S20-R29 (Armstrong–Mindermann
  Conjecture 9): a conclusion defined as a predicate, with nothing proved beyond an unfolding, is
  coverage **No**. (Conjecture 9 has since been stated at print's quantifier, `ConjectureNine`.)
- **Repair rule: grade against a repaired slip** (2026-11-14), on two conditions: the literal print
  must be *proved* wrong in Lean, with how it fails shown, and the repair must be shown necessary and
  minimal, not a different theorem. Each refutation lives in `docs/provenance/refutations/`, checked
  in CI outside the library. First case: S03-R08 (Ashby 11/9), refuted by `ashby-11-9-literal.lean`
  (|D| = |R| = 2, k = 1, table [[a,b],[b,a]], constant outcome), the repair tied to §11/7.
- **Ashby 11/11 (S03-R10)** (2026-11-14): `hcol` (no repeat in a column) is Ashby's own condition
  (§11/5, book p. 206). Superseded 2026-11-20: channel capacity is rendered by a proxy, Mixed.
- **Repairs accepted 2026-11-20**, each with its Lean refutation of the literal print: 228 and 271
  (Peleg Example 2.3/3.6, `peleg-ex-2-3-literal.lean`), 246 (Peleg Theorem 3.5,
  `peleg-thm-3-5-literal.lean`), 172 (Skalse footnote 5, `skalse-footnote-5-literal.lean`), 035, 046,
  305 (Pauly Theorem 3.2 over an infinite outcome set, `pauly-thm-3-2-literal.lean`; Everitt
  Theorem 11, `everitt-thm-11-literal.lean`; Ashby 11/7, `ashby-11-7-literal.lean`), 180
  (`eu-lemma-b7-literal.lean`), 224 (`rice-literal.lean`), 201 (`cover-thomas-2-8-1-literal.lean`).
  254 (Regressional) was refuted but its repair was not minimal; it is graded under the reading ruled
  2026-11-22 (`ADJUDICATION-LOG.md`).

## Ruled 2026-11-21 (author)

- **R1 yes**: Ring–Orseau's "Σ_k w(t,k) < ∞" is absolute summability; `hw : Summable |w|` is print's own.
- **R8 yes**: at an infinite vertex set, "DAG / recursive application of the structural functions"
  means a well-founded parent relation; `IsWellFounded` is print's own.
- **R9 no**: utility sums, Def. 17's vertex sets and max_π are finite / over all policies as print
  presupposes; the finite-utility, finite-vertex and all-policies-measurable hypotheses have no effect.
- **R2 yes**: Ring–Orseau's v_t is the limit of the finite-depth values (the series value, "expected
  sum of future weighted utility values"), not any solution of the recursion; `infiniteValue` is print's object.
- **Repairs accepted** (each needs its Lean refutation of the literal print in
  `docs/provenance/refutations/` under the 2026-11-14 rule): 183 (H_D(R)), 025 (inside the finite
  remark), 091 ((3) about the Simple Model; (2) for non-degenerate G), 198 (attained over arbitrary E).
- **Agreed readings accepted 2026-11-21** (author: "where they agree, I agree", after the adversarial
  review by Codex, Grok and a fresh Opus, referee records not published): R3 yes (attainment
  presupposed), R4 no (least maximiser, not a well-founded order), R6 yes (prefix universal machine),
  R10 ∀π* ∃d, R12 total correctness, R15 yes, R16 (a) exact rational reward tables (021 still Narrower at
  irrational rewards; a hybrid coding is needed for Same), R17 yes. R14(b) was already settled by the
  2026-11-20 repair of 201. Still open (reviewers split): R5, R11, R13, R14(a).
- **Round 2 (2026-11-21, panel unanimous, accepted by the author's rule "where they agree, I agree")**:
  R5 yes (Statements 1 and 3 under footnote 5; the posterior step is not owed). Readings confirmed 3-0:
  160 (the convergence sentence is a hedged expectation), 240 (mistakes per step), 090 (one fixed
  mechanism table). Still split: R13 (135; 2-1 stays below), R14(a) (314; 2-1 no), 087 window
  completion (2-1 indicator), 193 "episodic" (open). 005: no route to Same.
- **Round 3 (2026-11-21, author: "do as recommended")**: window completion for A_rl is the window
  indicator (rows 087, 131); Appendix A's "If L is reasonable" includes the sketch's overhead
  assumptions (row 286); infinite-entropy variables are out of scope for Cover–Thomas 2.10.1
  (row 314). Still open: R13 (row 135).

## Ruled 2026-11-23 (author: "as recommended")

Reading questions from the completion pass (`v6-impact/OUTCOME.md`, last section):

- 095 (Orseau-Ring, reinforcement-learning agent): normalization of rewards to [0, 1] "without loss
  of generality" is a modeling convention, not an asserted invariance. Wider.
- 123 (Zhuang-Hadfield-Menell, incremental optimization): the rate function is kinematic only, on
  closed time [0, inf). Wider.
- 181, 164 (knowledge-seeking agent): the entropy, Kolmogorov-complexity and identification sentences
  explain the objective u = -rho(h); they are not separate claims. Wider.
- 255 (Carter-Shnayderman thesis 1): domination needs the capacity to interfere, not its exercise.
  Wider.
- 229 (Armstrong-Mindermann B.2): "not fully rational" is suboptimality from the given start state
  for the true reward, as print's "strictly less" requires. Same.
- 281 (Alfonseca et al., Algorithm 3): print supplies the composition of harm ("since the execution
  of T(I) cannot harm humans"). Same.
- 240 (Orseau-Ring, footnote 6): "only one environment" means exactly one. Mixed either way.

## Readings of print (open)

| # | Question | Rows | Yes → | No → | Rec. |
|---|---|---|---|---|---|
| R1 | Ring–Orseau "it must be summable: Σ_k w(t,k) < ∞" means absolute summability (w ≥ 0)? | 073, 109, 160, 240 | `hw : Summable |w|` is print's own; 109 Wider; the others lose this axis | signed w in scope; print's own v diverges on w = (−1)^k/(k+1), so the wider statement is false (unclosable) | yes: only reading under which v is finite for every u ∈ [0,1] |
| R3 | "takes the action with the highest value" presupposes the maximum is attained? | 160, 240 | `InfAttains` is print's | no maximiser on Action = ℕ, reward 1 − 1/(a+2): A^μ undefined; unclosable | yes |
| R4 | Footnote 4 "ties broken lexicographically" means a well-founded order (shortlex)? | 028 | axis drops | plain dictionary order on strings is not well-founded; closure S anyway (least maximiser) | either; closure is cheap |
| R5 | Statements 1 and 3 graded under footnote 5 ("P(DB) as high as needed"), not the Arguments' thresholds 1/(2 − r̄) / Q_B > Q_h/2? Also: does footnote 5 discharge the step ρ(q_b) < ρ(Q_B) ⇒ P(DB) > 1/2? | 207 | closes with one lemma (S–M); 207's step not owed | Arguments' threshold is false above depth 0 (witness: window 2, prior 0.6, refusing worth 1.4 > 1.2): repair candidate | yes |
| R6 | AIXI's program set Q is that of a prefix universal machine (Σ 2^−|q| finite)? | 087 | `UniquelyDecodable`/summability is print's; no defect | {0, 01, 10} is an instance; 087 still uncovered for Q = all strings (ξ([]) = ∞) | yes |
| R8 | At an infinite vertex set, "DAG / recursive application of structural functions" means well-founded? | 117, 301, 311 | `IsWellFounded` is print's | ℤ-chain: two solutions, print's evaluation names no value; unclosable | yes |
| R9 | U := Σ_{U∈𝐔} U admits infinitely many utility nodes with a convergent sum? Def. 17 admits infinite vertex sets? max_π ranges only over policies whose expectation exists? | 012, 297, 301, 311 | each is an M-size Lean closure (tsum/measurable-policy layers) | finite sums/vertex sets are print's; 297 grades Wider | no (finite) |
| R10 | Def. 17 (2): free d chosen after π* (∀π* ∃d, as `HasICIAt`)? | 297 | current Lean is print's | ∃d ∀π* needs new definitions (S) | yes |
| R11 | Pearl "a finite number of discrete variables" allows countably-valued variables? | 090 | L-size Discrete marginal layer owed | `Fin (dim c)` is print's; row Wider | no |

**R11 decides no row since wave 7 (2026-11-22):** `Causal.DiscreteMarginal` states Properties 1 and 2 at arbitrary value types, so 090, 205 and 293 are Wider under either answer (ruladj93). Still unruled, no longer owed. **Ashby §11/6 (row 287)** ruled 2026-11-22: repair accepted (`ashby-11-6-literal.lean`).
| R12 | Melo et al.: P is total correctness (every input gets an accepted output; library `judgeSpec`)? | 083 (SW, conditional) | literal M′ exists (wave-4 corollary); no repair | P is co-r.e.; literal M′ refuted (`refutations/melo-mprime-literal.lean`); accept complement repair? | yes |
| R13 | Armstrong–Mindermann "reasonable pair" includes Conjecture 9's "not close to minimal"? | 135 | row Wider | row Mixed, unclosable (fails at (greedy, R_π)); declaration frozen | — |
| R14 | Cover–Thomas: log|𝒳| makes X finite for the whole of 2.10.1? Infinite-entropy (infinite mutual information) variables in scope for 2.10.1 and the 2.8.1 equality case? | 314, 201 | row Same | geometric X excluded (M closure); with infinite entropy the real-valued 2.10.1 is false (p(n) ∝ 1/(n log² n)), and 2.8.1's equality case fails at X = Y = (A,B), Z = A, H(A) = ∞ (I(X;Y) = I(X;Z) = ∞ but I(X;Y|Z) > 0), so 201's `hfin` is unclosable | yes / no |
| R15 | An open conjecture row is graded by its Prop rendering at print's quantifier? | 235 | covered once the Prop exists (S) | needs a proof | yes (2026-11-14 ruling + "conjectures Same as print") |
| R16 | Armstrong–Mindermann complexity of planners: which coding? (a) exact rational reward tables, (b) programs on computable-real reward codes (wave 4's `DescribedComplexity`) | 021 | (a): claim (2) provable; computable irrational rewards get K = ⊤ | (b): no program computes the greedy planner (max of computable reals), so K(p_g, R) = ⊤ and claim (1) holds at the defect's instance only vacuously | (a), several hundred lines |
| R17 | Ashby §11/8 repaired minimum (198): may the attaining E live on an extended sample space carrying a copy of (D, R) with the same joint law (Ashby's quantities are distributions)? | 198 (SW, conditional) | the repair is proved (`exists_entropy_eq_sub_of_condEntropy_eq_zero`); row Same | on the original space attainment can fail (`no_attaining_on_three`): the repaired print is itself false there | yes |
| R18 | Ring–Orseau Statement 4: must the prior ρ : Q → [0,1] be universal (every program positive, or dominance), or may it be any prior over programs, as p. 3's typing and the general A^ρ allow? | 005 (NoScope either way) | statement undecided at universal priors; no repair | Fable (Part 94) derives a countermodel at m = 2 (exact rationals, 40-program truncation, not Lean): the agent programs the box at every step; print false, a repair ruling and a Lean refutation (M–L) would be owed; Codex independently finds final.jsonl's proposed comparison fails even with a universal tail | open; grade unaffected |

## Repairs of false print (literal refuted by a witness; refutation file to be written on "accept")

| Row | Print | Witness | Repair |
|---|---|---|---|
| 183 (Ashby §11/8) | last display with H_D(E) | D, E independent fair bits, R constant | H_D(R), as the two preceding lines and "H_D(R) = 0" indicate |
| 025 (Breuer) | "properly included ⇒ strictly more states" | O = ℕ×Bool, A = ℕ, `readNat` (Examples/Knowledge/Embedded.lean) | read inside the finite remark |
| 091 (Manheim–Garrabrant) | (3) for every proxy M ≠ G; (2) strict | M = G + 1_{G<0}; constant G | (3) about the Simple Model; (2) for non-degenerate G |
| 198 (Ashby §11/8) | "H(E)'s minimum is H(D) − H(R)" attained | column-injective tables, D uniform on 3 | attained over arbitrary E only |

## Overrides (optional)

- 16 rows decided by the contested rule (side shared by Codex and Grok): 070, 117, 123, 206, 259,
  270, 280, 304 (full run), 220 (corrected), 131, 160, 209, 314 (wave 3), 087 (wave 4), 073, 193 (wave 4b).
- 148: SW at confidence 3; the adjudicator notes its witness would make Pearl's own Property 2 (1.39)
  false under the where-defined reading.
- 083: wave-4 blind graders unanimous Same, on the library's `judgeSpec` (total-correctness)
  reading; if R12 goes to the every-output-accepted reading, literal print is refuted and the row
  must be regraded against the repair.
- 263: SW adjudicated with missing context (where the source invokes "lim = sup").
