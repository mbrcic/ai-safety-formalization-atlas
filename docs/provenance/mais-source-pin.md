# The pinned MAIS source

Every MAIS-derived conjecture in `conjectures.yaml` is graded against the exact
artifacts recorded here. Before 2026-08-20 there was no pin: every locator in
`registry.yaml` pointed at `.../blob/main/...` or `.../tree/main/...`, a moving
branch. The source could change under the atlas and no gate would notice, while
Richens & Everitt 2024 — a far more stable artifact — already carried a `sha256`
for each of its two texts. That asymmetry is what this file removes.

## Repository revision

| field | value |
|---|---|
| repository | `github.com/lionellevine/MAIS` |
| commit | `9dd29f8bf5ccd1e7701e300039b09ed4096b6516` |
| committed | 2026-08-10T07:35:54Z |
| subject | *Promote O62 progress report PDF link* |
| pinned by the atlas | 2026-08-20 |

Every locator below is a permalink at that commit, so the bytes are fixed even if
`main` moves.

**What the pin does and does not certify.** It fixes what is graded *from now
on*. The causal grading done on 2026-08-19 and 2026-08-20 read `main` at the
time, and no record of which revision that was exists — that is the defect this
file closes, and it cannot close it retroactively. `9dd29f8` is the repository
head as of 2026-08-20 and is therefore what those readings almost certainly saw,
but that is an inference, not a check. Treat every pre-2026-08-20 grade as
verified against these bytes only to the extent it has been re-read since.

## The agendas — the statement sources

MAIS-A2 is where all but one of the conjectures are actually stated; MAIS-A3
carries the remaining one, `prob:samples` (MAIS-O38), which has no causal content
and shares no vocabulary with the A2 rows. The `open-problems/*.md` files are
one-page restatements that point back into whichever agenda states them.

| artifact | sha256 |
|---|---|
| `agendas/A2/MAIS-A2.tex` | `d61be3eed51f618dd3b9389693b14e066e89a9cef5e89985b4226fff658c3c4f` |
| `agendas/A2/MAIS-A2.pdf` | `91fcefc283db02f377c723120357bb3dc67836604986cfc17f6c0573bdaf6bed` |
| `agendas/A3/MAIS-A3.tex` | `146f0cc95a0a5eb0cf3b2660c32d591169b0e346571b80ee63723a9906371387` |

**A3 is pinned by its `.tex` only.** The A2 pair is hashed so a discrepancy
between text and render is detectable; no A3 PDF is hashed here, because nothing
in this repository grades against one. Read from A3 on 2026-08-27: `\Oid{38}`,
`\label{prob:samples}`, at line 290 — the line the open-problem page links to.

The `.tex` is the text this atlas grades against, because it carries the
statements verbatim and the `.pdf` is its render. Both are hashed so a
discrepancy between them is detectable.

**Which numbered statement is which**, read from the pinned `.tex`:

| MAIS-O | A2 environment | label |
|---|---|---|
| O23 | `\begin{question}` | `q:ident` |
| O24 | `\begin{problem}` | `prob:effective` |
| O25 | `\begin{problem}` | `prob:exact` |
| O26 | `\begin{conjecture}` | `conj:exact` |
| O27 | `\begin{problem}` | `prob:floor` |
| O29 | `\begin{problem}` | `prob:boltzmann` |
| O31 | `\begin{question}` | `q:chain` |
| O34 | `\begin{problem}` | `prob:starter-set` |

And from the pinned A3 `.tex`:

| MAIS-O | A3 environment | label |
|---|---|---|
| O38 | `\begin{problem}` | `prob:samples` |

Supporting definitions the atlas transcribes: `def:cbn` (causal Bayesian
network), `def:local` (local interventions, masks, profiles, mixtures),
`def:cid` (binary causal influence diagram — skeleton, model, policy, value,
regret), `def:margin` ((M1)–(M6)), `def:twovar` (the two-variable family
`𝕄₂(λ)`), and `prop:equiv` (behaviour is equivalent to the transform).

## Open-problem pages

| file | sha256 |
|---|---|
| `open-problems/MAIS-O23.md` | `80a6aa32e387e12494e24c3c693cd2886aabe50a0889155affedfdf8e88cfdea` |
| `open-problems/MAIS-O25.md` | `6dcf7b96ba840a46e294ff21fd857fbda8dfbac39e4124567da7ff985629f734` |
| `open-problems/MAIS-O26.md` | `3b38114b5b89f0f9c18ef13d8042c2e6b2907a90232bb2ba0f9e543a4720a013` |
| `open-problems/MAIS-O29.md` | `7f493b9c7d19e1e56ada160d0bff6905e26f4a271b5e84919ba8e931d9fd6a3f` |
| `open-problems/MAIS-O31.md` | `9b20c862d2ba6f4b701fa9f87590e7c2467e8d0c1bd5fcee18f5d0a5d15bfe8b` |
| `open-problems/MAIS-O34.md` | `8c9a8e739611acf96c692f4adce0691bd6fafee53783533c1817cd5ba8989ac1` |
| `open-problems/MAIS-O38.md` | `cea6784554724ce4e67b8967a9fe6fba6959e70a32494dc97b0b8fd3685c4d43` |

## Issues

Issue bodies are editable in place and carry no revision history a permalink can
address, so each body is hashed as read on 2026-08-20. A later edit changes the
hash and invalidates the grading that rests on it — which is the point.

| issue | title | author | body sha256 |
|---|---|---|---|
| [#4](https://github.com/lionellevine/MAIS/issues/4) | MAIS-O34: exact fibers, regret geometry, and a single graph-threshold program | Robby955 | `f425da83395b457feb5615c9beed703675a977967890ebe1b97dd61efdd0b328` |
| [#6](https://github.com/lionellevine/MAIS/issues/6) | MAIS-O23: candidate negative resolution — a three-DAG behavioral collision | kumino | `4fd639c4322a3a3bd1b27fe6f14ee3de902961e0013485395e461d7cdc739a9b` |
| [#8](https://github.com/lionellevine/MAIS/issues/8) | MAIS-O31: candidate complete solution — generic chamber classification for one intervention in a binary chain | kumino | `8e2e688eaac1a72f915aa787ad1e74676e6b72eff4f2796394e95b0a83fb8a96` |
| [#30](https://github.com/lionellevine/MAIS/issues/30) | MAIS-O38 candidate complete solution: m^3+2m fixed codes suffice for every sparsity k < m | 26david26 | `6e2db10eb10242c075ca331fcf87a604511b9b31df3d55a5c4b0d2d2d95d05ab` |

Issue [#30](https://github.com/lionellevine/MAIS/issues/30)'s body was read on **2026-08-27**, re-fetched and confirmed unedited on
**2026-08-30** (`updated_at` is `2026-08-26T11:16:22Z`, before the first
reading). It sits in a different relation to its row from the other three: it is
`context_source_ref` for CONJ-025 rather than the graded artifact.
[`mais-o38-transcription.md`](mais-o38-transcription.md) records its influence in
full, corrected on 2026-08-30. Nothing in the Lean depends on the issue being
correct, so an edit to its body invalidates a provenance note rather than a
grade.

**The attached proof note is pinned separately.** The issue links a 15-page PDF
carrying the full argument; the body alone states only the claim.

| artifact | value |
|---|---|
| file | `o38-note.pdf`, attachment of issue [#30](https://github.com/lionellevine/MAIS/issues/30) |
| url | `https://github.com/user-attachments/files/31462612/o38-note.pdf` |
| sha256 | `2ba4179f312b7e5c9fa87bcecc0702b409d2ec4fdab7d0f06e9ae387eed422ca` |
| pages / producer | 15, `pdfTeX-1.40.28`, created `2026-08-26T12:08:34+02:00` |
| read | 2026-08-30 |

The note was read in full on 2026-08-30 and no gap was found; that reading is a
triage by one reader, not a referee report, and it is recorded as such rather
than as a check. What it established, and what the atlas now carries in Lean, is
in [`mais-o38-transcription.md`](mais-o38-transcription.md).

The three 2026-08-20 issue bodies were re-fetched on 2026-08-27 and all three
hashes above still match, which is a check on this table rather than on any
verdict.

**Comments.** Issues [#6](https://github.com/lionellevine/MAIS/issues/6), [#8](https://github.com/lionellevine/MAIS/issues/8) and [#30](https://github.com/lionellevine/MAIS/issues/30) carry none at their recorded readings. Issue [#4](https://github.com/lionellevine/MAIS/issues/4)
carries one, by the same author, saying that LaTeX may not render on mobile and
pointing at the PDF ([`#issuecomment-5170099225`](https://github.com/lionellevine/MAIS/issues/4#issuecomment-5170099225),
body sha256 `e290bb83bd980cc9a9b8a3610e21ec6e26a0aa5c3d2e036db10b2610d909bca8`).
It carries no mathematical claim and is graded against by nothing; it is
recorded here only so that "read and judged irrelevant" is distinguishable from
"never seen". It is not part of the candidate a conjecture row
transcribes, and it is kept out of the table of artifacts that *are* graded
against. Hashing it protects less than the table suggested: it would detect an edit
to this one comment and would not notice a new one, and nothing here watches for
that.

### The candidate the atlas had not read

Issue [#7](https://github.com/lionellevine/MAIS/issues/7), *MAIS-O24: candidate
negative resolution — clauses (a) and (c) are incompatible as written*, by
kumino, body sha256 `68e65b119a8923dd997e2ea75daea5331145706674a44ecc6d3f7c7b89a80ee7`, no comments at the
pinned reading. It is named by `open-problems/MAIS-O24.md` at this very commit; see
[`mais-o24-statability.md`](mais-o24-statability.md) for what it claims and what
of it has been checked.

Its argument lives in an attachment rather than in the pinned tree, so the
attachment is hashed separately and its own problem revision recorded, because
that revision is not this pin:

| artifact | sha256 | grades MAIS-O24 at |
|---|---|---|
| `MAIS-O24-candidate-solution.pdf` | `fd096dea004135fbbed054619857b307881d6432925d1ff1cae5ae3f45d16477` | `43016a3e5c94edfca55ba49bd3e16770f7ac5dae` |

`open-problems/MAIS-O24.md` is byte-identical between `43016a3e` and this pin
except for the status line, so the difference in revision does not put the
candidate and the atlas on different problems.

## What the pin is for

The rule this repository now works to: **a definition transcribing a source
definition, and a conjecture stated to be doubted or proved, must have scope
`Same` as the printed statement. A theorem may be wider — that only increases the
reach of the tooling.** A `Same` verdict is a claim about a specific artifact, and
it is unfalsifiable without one. That is what this file supplies.

Re-reading the source is therefore a dated event with a checkable result. To
advance the pin: fetch the artifacts at the new commit, diff the hashes, and
regrade only the conjectures whose statements moved.
