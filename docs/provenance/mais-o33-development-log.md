# How MAIS-O24 and MAIS-O33 were built, and what went wrong on the way

The two results are recorded in
[`mais-o24-refutation.md`](mais-o24-refutation.md) and
[`mais-o33-refutation.md`](mais-o33-refutation.md); the ledger rows are
`CONJ-012`, `CONJ-003` and `CONJ-023`. This file records the **process** instead,
because the finished commits hide it: sixteen commits were squashed to two before
publication, and every defect found along the way disappeared with them.

It is kept for one reason. Six of the defects below were not Lean errors — the
build was green each time — and five of the six were found only by **re-reading
the printed source against the Lean**, which is what each of the five review
passes below was. No gate found them, and no gate could have. They fall into four classes that will recur on the next
row, and the point of writing them down is to catch them earlier next time.

## The four defect classes

### 1. A quantifier withheld from a supplied datum

**The failure.** A structure field is given fewer arguments than print gives the
object it transcribes. The type is then *narrower* than print's, an impossibility
proved over it does not transfer, and nothing in the build notices, because the
narrow statement is perfectly well-typed and perfectly provable.

**Twice on this range.**

- `GoalPolicy` read state histories where print's policy reads the trajectory
  prefix `(s₀, a₀, …, s_t)`. Recorded as a safe reading with a direction
  argument, and the direction argument was wrong: `(δ,n)`-boundedness compares
  against `max_{π'}` over *the same class*, so narrowing the class lowers the
  threshold too and the two changes pull opposite ways. Closed by proof —
  `inducedPolicy`, `optimalProbFull_eq`, `isDeltaBoundedFull_lift_iff`.
- `UniformAnalyst.strategy` and `.estimator` took `(𝐒, 𝐀, n)` where print's
  instance is `(𝐒, 𝐀, n, δ)`. A δ-oblivious protocol is strictly weaker, and
  `UniformlyTolerableWithin` could not repair it, because an arbitrary predicate
  `C` restricts an already-narrowed type rather than widening it. Fixed by
  passing `δ`; only the query *bound* stays δ-free, matching print's
  `p(|𝐒|,|𝐀|,n)`.

The same class was caught twice before this range on MAIS-O24's clause (b)
threshold, once graded a widening and once a narrowing; both gradings are
recorded in `Causal/EffectiveGenericity.lean`'s own docstring.

**What to do.** For every field of a solution or protocol bundle, list print's
arguments for that object and diff them against the Lean binders. Do it from the
printed sentence, not from the Lean — the Lean is what is being checked. A
`⨆`-shaped threshold is the tell: if the printed clause compares against a
maximum over the class you are narrowing, the transfer fails.

### 2. A convention mistaken for a proof

**The failure.** Lean totalises what print leaves partial, the totalised value
happens to be the right one, and the theorem reads as a proof of print's sentence
when it is a proof about the convention.

**Here.** `etaStar = sSup {η | 0 ≤ η ∧ UniformlyTolerable η}`, and
`Real.sSup ∅ = 0`. So `etaStar = 0` is provable *even if nothing at all were
tolerable* — including `η = 0`. Print's `sup{η : η uniformly tolerable}` is a
supremum print takes to be over a nonempty set, because print asserts the
uncorrupted baseline before posing the problem.

**What to do.** Name the missing premise as a `Prop`
(`maisO33_baselineTolerable`) and prove the conditional
(`maisO33_etaStarIsZeroGivenBaseline`), so the dependence is visible to the build
rather than to a reader of a note. Do not add the premise to the row's own `Prop`:
print asserts the baseline rather than assuming it, so a hypothesis there would
launder a narrowing.

### 3. Stale prose left standing under its own correction

**The failure — the most frequent one on this range, four separate occurrences.**
A sentence is corrected by *appending* the correction instead of marking the
original, so the file says both things. Found on re-reading: the O26 coverage cell
still asking for an O24 solution to be exhibited, two paragraphs after the row
recorded that as impossible; `CONJ-003`'s `refutation` and `source_note` each
carrying "may currently be vacuously true" beside "IS vacuously true"; a
retracted `η*_C` argument still standing in `source_note` after the note had been
fixed; and the source pin's heading "the candidate the atlas had not read" over
an issue whose claim was by then machine-checked.

**Why it kept happening.** Every MAIS argument exists in **four** places: the
provenance note, `conjectures.yaml`'s `resolution`, its `source_note`, and
`mais-a2-statement-coverage.md`. The ledger copies are long single-line JSON
strings, so a stale paragraph is invisible in a diff.

**What to do.** After retracting an argument, grep its own notation — the symbol,
the declaration name — across all four, and read what each says. Correct in place
with a dated marker rather than appending, so the change of state stays visible.

### 4. A hash without its method

**The failure.** `docs/provenance/mais-source-pin.md` recorded issue-body
digests with no statement of how they were computed. They are
`gh issue view N --json body -q .body | sha256sum`, and `jq`'s raw output appends
a newline, so each is `sha256(body ‖ "\n")`. Anyone verifying the pin the obvious
way — hashing the API's `body` field — gets a different digest and concludes the
issue was edited. For issue #7 that is `a8f4aeee…` against the recorded
`68e65b11…`.

**What to do.** Record the command beside any hash of a remote artifact. A digest
whose method is undocumented is not a pin; it is a number.

## What the two changes of instance bought

Not a defect, and the one thing on this range worth repeating deliberately. A
refutation of a universally quantified printed claim **chooses its instance**, and
choosing better removed two dependencies the audit had priced as projects:

- **`δ = 1/2` rather than the candidate's `δ = 0`.** At `δ = 0` the boundedness
  clause demands exact optimality, which needs an optimal-policy-existence
  theorem for reachability objectives on a finite controlled Markov process.
  Mathlib has none. At any `δ > 0`, supremum approximation suffices.
- **Action-independent kernels rather than the candidate's one skewed row.** The
  splice needs the trajectory law to agree across policies; on print's own
  action-independent class it is literally the same measure, so the congruence
  lemma for `ProbabilityTheory.Kernel.traj` that the audit called *the* blocker
  was never needed.

Before formalizing a missing library lemma for a counterexample, ask which
admissible instance makes it unnecessary.

## The sixteen commits, in order

The full history is kept privately and is not published: a reader of this
repository sees the two squashed commits, and the sequence below is the record of
what they contain. Step 7 is where the answer landed; steps 8-16 are what five
re-readings of the printed source then changed.

| # | what it did |
|---|---|
| 1 | MAIS-O24 has no solution; MAIS-O26 vacuous because of it. Repairs the candidate's last step (`μ` before `u`) |
| 2 | Audit of MAIS-O33's candidate; the two instance changes identified |
| 3 | MAIS-A2's goal syntax; the candidate's counting lemma machine-checked |
| 4 | The environment, and the two kernels the candidate separates |
| 5 | Trajectory law and print's `(δ,n)`-bounded agents |
| 6 | The three readings recorded; the history axis closed by proof |
| 7 | **MAIS-O33 answered**: no positive corruption fraction is uniformly tolerable |
| 8 | Review 1: measurability proved; the analyst-class widening closed; issue #9 pinned |
| 9 | Review 2: the `thm:rabe` dependence made a hypothesis; *algorithm* read from `subsec:queries` |
| 10 | Review 3: **δ passed to the analyst**; the determine-clause graded at the conditional |
| 11 | Review 3: the two ledger copies the previous commit corrected only in the note |
| 12 | What closing the `η = 0` baseline actually takes |
| 13 | Review 4: O26 matrix cell; statement lock; issue #7's stale heading |
| 14 | Review 4: the hashing convention recorded |
| 15 | Review 5: O26 vacuity sentences put in the past; the right declaration named per O33 clause |
| 16 | This log; then the self-referential correction markers stripped from the notes and the ledger, leaving the process recorded here and the result stated there |

Commits 8–15 are all review response. Commit 7 was green, gated and
axiom-clean — and wrong in two ways that mattered, one of which would have
blocked the transfer to print entirely.

## What the gates did and did not catch

Green throughout: `lake build`, every target in `scripts/lean_build_targets.txt`,
`agent_gate.sh`, `check_print_axioms.py`. They caught two real things — a
positional `answer_correct` list that had grown to two entries, and a Mathlib
name (`le_csSup`) written into the ledger where `check_cited_declarations`
requires an atlas declaration.

They caught none of the four defect classes above. Scope, fidelity and the
statement–claim–proof distinction are not machine-checkable against a printed
source; they are checkable only by reading the source again, which is what each
of those five passes amounted to.
