# Mapping from the old scope labels to SPEC v6 (§10(d))

SPEC v6 (`spec/SPEC-v6.md`, sha256 prefix `4bf67c231af3fee6` as graded in the v6 impact pass)
replaces the coverage audit's single Scope scale and SPEC v5. This file says how every old label
carries over, and which rows were regraded.

## Old audit scale (preamble of `source-coverage-audit.md`)

| Old | Old meaning | v6 |
|---|---|---|
| Wider | atlas statement implies print, not conversely | `Wider` when forward entailment is certified (§6); a carrier generalization that passes the transfer test (§7.1) is representation, so `Same` |
| Same | they are the same statement | `Same` when both directions are certified |
| Narrower | print implies atlas, not conversely | `Narrower` when reverse entailment is certified; otherwise `Mixed`; an unproved assumed hypothesis is `conditional` (K5) |
| Mixed | wider on one axis, narrower on another (axes undefined) | `Mixed` = neither direction certified; the axes say which difference |
| Beyond | atlas proves what the source does not state | role `no-print`, scope `Beyond`, coverage `—` (unchanged) |
| — | no atlas statement | unchanged: coverage `No`, ungraded, not owed |
| (none) | — | new: `None` (cited Lean proves nothing of print, B = none; graded, below print, owed); `Refuted` (literal print refuted in Lean, no repair ruled) |

**Coverage** was graded independently of scope (the audit held Partial/Same, Partial/Wider,
Yes/Narrower, Yes/Mixed cells). Under v6 coverage is computed: `Yes` iff Same or Wider, `No` iff None
or Refuted, else `Partial`. Every Coverage cell is recomputed at migration; no grading judgement is
involved.

**Retired rules.** "The sample space is not a scope axis" becomes the transfer test (§7.1): an
arbitrary sample space is representation when the pushforward transfers print's conclusion (E27).
"Stability" becomes the change rule (§10). "Same with a note" for a definition with a different
defining predicate becomes `Mixed` (§7.2).

## SPEC v5 labels

Axes C, A, B keep their names and values, except: B1 now gives `missing` (not `incomparable`) for a
proxy component; K5 (vacuity) and K6 (substantive Partial) can turn a v5 Mixed into `None`; the
certification step (§6) can replace the matrix label. Flags added: `conditional`, `argued`, `strict`,
`repaired`, `proof` (conjectures). v5's "—" for B = none is spelled `None`.

## Which rows were regraded (`v6-impact/`)

the selection script (not published) tags every row a v6 change can move, from its deciding record:
- `carrier`: Wider with applicability broader and conclusion same, the reason naming a carrier
  generalization (transfer test, A6, polarity A10);
- `reading`: Same/Wider with an unruled reading or open question (conservative default, §7.6);
- `provisional`: Same/Wider with missing context or aggregation sensitivity;
- `argued`: Same/Wider whose reasons rest on a step off the closed list (§7.9);
- `proxy`: a proxy object (B1, K6);
- `definition`: a definition row with a defining condition graded different (§7.2).

263 rows are tagged: 106 with a tag other than `carrier` go to track F (full v6 regrade, two blind
graders and grounded adjudication); 157 tagged `carrier` only go to track T (transfer and polarity
check, one grader; any row reported existential, negative-position, excluded-instance or below print
moves to track F). The 52 untagged rows carry over with their current grade, scope and coverage
recomputed by the table above. A control sample of 8 untagged rows (`v6-impact/control.json`) is
graded in track F; if any of them moves, the selection is leaky and is widened before migration.
