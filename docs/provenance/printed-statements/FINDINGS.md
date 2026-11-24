# What the transcription from page images found (2026-11-14)

All 315 graded rows were transcribed from rendered PDF pages (31 files in this
folder) and second-read on 2026-11-15 (§7). Reading the page instead of
the text layer surfaced the items below. Each is also recorded in the `note`,
`context` or an excerpt of the entry it concerns; this file is the index, sorted
by what it means for grading. Row ids are the regrade's (`regrade-2026-11/`).

**Status: leads, not verdicts.** Each item was raised by one first reader. Items
marked **[verified]** were re-checked against the page image (or, for a claim of
absence, a search of the whole document) by a second reader on 2026-11-14; the
rest wait for the second reading. A lead changes no grade until it is verified,
and a printed claim counts as wrong only once refuted (ruling of 2026-11-14).

## 1. The audit cites or transcribes something the page does not say

These change what a row is graded against.

| Row | Finding |
|---|---|
| S23-R14 | **[verified]** The quoted fragment ("can obscure relevant information about the power structure") is in the companion two-agent paper (arXiv:2603.04160v2, p. 1), not in arXiv:2607.10567. The audit already says so in its provenance note (audit L3037, L3080); the defect is the source card and this row's mapping, which point at the general-CGF file. The entry transcribes the §1.2 paragraph the locator names. |
| S23-R05 | "Enlarging a coalition cannot destroy an alpha power" is the gloss on a defining condition (Def. 12 item 4) of α-representative frames, not a result about general concurrent game frames. |
| S14-R07 | **[verified]** Prop. 2 does not say the α-effectivity function is *truly* playable; the Atlas paraphrase adds it (true playability is defined later, Def. 8, p. 13). |
| S14-R11 | The Atlas quote is the sentence before Prop. 6 ("on finite domains playability and true playability coincide"); Prop. 6 states the same for playable effectivity functions on a finite domain. A locator nuance, not a content change. |
| S14-R12 | The "§3.1 counterexample" is the proof of Prop. 4 (pp. 9–10). |
| S05-R03 | **[verified transcription]** "(30)+(31)": neither equation contains $L_C$ or a conditional mutual information; (30) is $H(X'|X,C) \le H(Z|X,C) = H(Z)$, (31) a chain rule for $H(X',Z|X,C)$. The Atlas paraphrase rewrites them through Theorem 3 on the same page ($L_C = I(X';Z|X,C)$, (32)); whether that rewriting is faithful is a grading question, not settled here. |
| S05-R14 | "below (50)" is below (51), inside the proof of Thm 10. |
| S03-R02 | The "multiplied form" is not printed in §11/5; the only general statement is the r/c sentence (= S03-R01). |
| S07-R02 | **[verified]** No printed statement exists: "Corollary" does not occur in Pearl ch. 1, and the pages citing (1.37) state no full-profile or point-mass consequence. `latex: null`. |
| S02-R09 | Locator "Example": no such label; an unlabelled paragraph continuing the Remark, (2.144). |
| S22-R07, R08 | Located in §II "A Simple Taxonomy" (p. 1047), not §III. |
| S24-R01 | Two sentences on different pages (abstract p. 1, end of proof p. 3) graded as one. |
| S05-R01, R02 | Both rows are the same printed sentence (Thm 2). |
| S19-R12 | Starts on p. 206, not only p. 207. |
| S16-R04 | Card page 17 is the appendix restatement; the original is pp. 4–5 (identical). |

Audit quotations that drop or alter printed content: S21-R16 (the ellipsis drops
the mathematics, "if $S \subset T \subset N$ then $E(S) \subset E(T)$"); S28-R11
(drops the opening clause "As the program R and the state of the world D are
arbitrarily complex,"); S23-R10 (silently drops "namely ε, S, D, SD,"); S08-R08
(drops ", written $(X \perp Y \mid Z)$" and the d-connection sentence); S08-R04,
S18-R03, S18-R05 (notation changed or subscript dropped); S22-R02, R03, R04, R14,
R15 (ellipses that drop content); S06-R08 (drops "Therefore").

## 2. Hypotheses the proof uses that the statement does not print

Readings by the first reader; none verified yet. Each would bear on axis A (a Lean hypothesis matching one of these may render print's
real assumption rather than narrow it, or the source's statement is wider than
its own proof). The passage is in the file as an excerpt.

| Row | Finding |
|---|---|
| S19-R10 | Breuer Prop. 2 states no meshing condition; its proof applies the Lemma, which assumes it. |
| S05 (Thm 2) | Touchette–Lloyd assume only purification; the proof at (30) uses "Z is chosen independently of X and C". |
| S16-R13 | Turner–Tadepalli Lemma B.10's hypothesis on $h$ is printed at the fixed $A$; the proof applies it at an arbitrary $X$ (eq. 41). |
| S16-R05 | Closure of Θ under permutation enters only in the proof of Prop. 3.4, whose last step ("apply lemma B.7") is circular as printed; probably Theorem 3.6. |
| S16-R16 | "Returns a probability" is used in the proof as monotonicity under inclusion. |
| S12-R03, R13, R27 | No nonzero-denominator condition, but the proofs of Lemmas 13 and 27 divide by $C(r|s)$. |
| S12-R05 | $s$ free in (3); the proof reads it as "for all $s$ with $B(s|a) > 0$". |
| S21-R23 | Surjectivity of $g$ is assumed in Def. 3.3 and not repeated in Thm 3.5; the appendix version states monotonicity for $E$ rather than $\gamma$. |
| S24-R04 | Melo et al. use "decides $P$" without defining $P$ or "decides". |
| S27-R21..R23 | The proof of Prop. 3 uses only the ⇒ direction of Prop. 2, which the paper says holds for arbitrary systems: whether the non-triviality hypothesis is needed. |
| S09-R12, R13 | Corrupted-reward Thm 11: the proof treats the policy as deterministic (the setup allows stochastic); complements staying inside the classes needs the uniform grid, unstated. |
| S20-R24 | Armstrong–Mindermann Prop. 7: the proof assumes a simplest compatible pair exists. |

## 3. What the source leaves undefined (silences that decide scope)

S27: $S \models \varphi$ and $\models \varphi$ are never defined (all states or the
initial state?), nor "objective formula"; matters for S27-R17, R21–R23.
S28: no criterion for "harms humans". S02: no $|\mathcal X| \ge 2$, though (2.132)
divides by $\log|\mathcal X|$. S16-R14: index range and finiteness unstated.
S16-R12: "monotonically increasing on its first argument" undefined. S08: "path"
undefined; whether $\mathbf{Desc}^V$ contains $V$. S04: the neighbourhood
definition says nothing about $n(x,x)$; SVW NFL3 has no sample length.
Touchette–Lloyd define no multivariate conditional entropy or conditional mutual
information (their reference is Cover & Thomas, 1st ed., 1991). S06-R03: $p_i \ge 0$
not printed; S06-R09: eq. (2)'s denominator can be 0. S08-R19: $d$ unquantified,
no positivity of $\Pr(\mathbf{pa}^D)$. S20-R12, R29, R36: "reasonable", "not close
to minimal", "high regret" have no threshold.

## 4. Candidate printed slips

Transcribed as printed. Only one is refuted: S03-R08 (`log V_R`;
`../refutations/ashby-11-9-literal.lean`). Every other item is a candidate; under
the ruling of 2026-11-14 a row is graded against a repair only once the literal
print is refuted and the repair shown necessary.

Candidates bearing on a graded statement: S03-R05 ($H_D(E)$ for $H_D(R)$ in §11/8);
S09-R14 ("induce the same measure" would be false for the measure of eq. (1),
which includes the true-reward coordinate; only the marginal on observed histories
agrees; not yet refuted); S09-R15 (undotted $G_t$ sums from 1, $\dot G_t$ from 0); S19-R03, R10
(membership signs in the definition of distinguishing); S21-R20 ($B \subset S$ for
$B \subset A$); S25 eq. (6) (rank of a product written as the minimum of the ranks;
intended: $T$ nonsingular); S05 eq. (53) (closed for open, also in arXiv); S26-R06
(footnote 5 overstates Def. 2); S27-R10 (⇒ for ⇐); S11-R12 (sets compared where
masses are meant); S13-R08 vs S11 (`k + t = m` vs `k − t = m`); S20-R02, R11, R20,
R21. Typographical slips are in the entries' notes.

## 5. Source versions and pins

- **S06, S08 [verified]:** `source-cards/map.tsv` and the cards used the arXiv files; the
  audit pins the published PDFs (audit L1036, L1181). Transcribed from the published versions, which
  match arXiv on every graded row (S08 up to column order); the transcriptions here are the
  record.
- **Ashby:** the PDF is the second impression, 1957 (copyright 1956); "1961" is only
  in the file name. **Decided 2026-11-14 (author): cite 1957**; the audit, the Lean
  module docstrings and the provenance notes now say 1956, second impression 1957.
- **Peleg:** document dated 1998, file `peleg1997.pdf`. **Breuer:** document 1995,
  file `PhilSci1993-…`. **SVW:** no venue, year or page numbers printed. **Orseau–Ring,
  Goranko–Jamroga–Turrini:** author versions with no venue printed; venue taken
  from the audit and marked so. **Klamka:** volume and issue not printed.
- **S11 vs S13** (Ring–Orseau, Orseau–Ring): different scope for the same objects:
  $\rho : Q \to (0,1]$ "must be finite" vs $[0,1]$; $t = |h|$ vs $t_h = |h| + 1$;
  equation numbers (1) and (3) swapped.

## 6. Why the source cards' quotes are superseded

The cards' quotes came from `pdftotext`. Measured against the images: Pauly's
text layer is unusable throughout (custom font encoding); Klamka's quotes splice
the neighbouring article; Breuer's and Peleg's formulas are OCR-corrupted; in many
others `≠` becomes `=` or `6=`, `≤` becomes `6`, primes become `0`, ε, Σ and
displayed math are dropped, and two-column pages splice the other column into
the sentence. Several of these the card had marked "faithful". The cards remain
useful as locators and for their recorded silences; the print is the YAML here.

## 7. Second reading (2026-11-15)

**Method.** Every entry was transcribed a second time from the same page image by
a reader that never saw the first reading, and compared token by token after
notation normalisation (`\leq` = `\le`, `\left`/`\right` dropped, and so on).
Wherever the two disagreed on anything but notation, the page decided: a crop at
250--600 dpi, or the text layer where it is reliable for words, or the font a
glyph is drawn from where the image alone was ambiguous.

- Statements (315). Codex read all 314 printed rows blind from the label and the
  audit locator; Grok read 110 of them (it stopped before the rest). A
  first-reading token counted as read twice only inside a matching run of at
  least three tokens. The 121 rows that failed this (the reader had stopped
  earlier or started later) were read again by Codex, told the passage's first
  and last eight words; those sixteen words are therefore not independent.
  S07-R02 has no printed statement, which a search of the chapter established.
- Definitions and excerpts (156): Codex, anchored the same way.
- `source.standing` quotes (175): 93 match the text layer word for word; 77 were
  read again by Codex; for 8 no Codex reading was made and only their words are
  confirmed (text layer), not their mathematics: the coherence formulas of
  Wooldridge and van der Hoek (a), and Turner and Tadepalli's $S_d$,
  $\mathbf{x}' \in \mathbb{R}^d$. The rest of `standing` is the first reader's
  summary, not transcription.

Each entry's `checked.by` names the readers it actually had.

**First-reading defects found** (all fixed):

| Kind | Entries |
|---|---|
| Wrong glyph | S21-R05: Peleg Example 2.7 prints Greek $\nu$ (drawn from the font of $\sigma$ and the braces), transcribed as Latin $v$, three times |
| Wrong word | SVW `standing`: "referred to as simply as" for "referred to simply as" |
| Wrong arrow | S03-R13: Ashby's first 11/14 diagram described with $\nwarrow$ where $\nearrow$ is printed; both diagrams are now drawn as arrays |
| Editorial text inside `latex` | S21-R05, S24-R01, S27-R10, and the definitions `am-def-kolmogorov`, `or-def-utility-horizon`, `peleg-thm-3.5-star`: page markers such as `[PDF 4, p. 70:]`; now `[\ldots]`, pages in `note` |
| Wrong page range | S27-R17 (starts PDF p. 14), S15-R06 (PDF pp. 4--6), S16-R05 (ends PDF p. 5) |

No first-reading error touches a symbol a grade rests on: S21-R05's $\nu$
only names a habit in an example. **Second readers' errors** were far more frequent and of a
consistent kind: they silently correct printed slips and spellings (Breuer's
$\not\ni$ to $\notin$, "exludes", "satisfices", "permissable", "measaure"), drop
calligraphic, typewriter and accent marks ($\mathcal{Q}$, $\mathtt{AG}$,
$\check r$, $\dot\Pi$), misread small glyphs ($A_{rl}$ as $A_{rt}$; Everitt et al.'s printed
$\sup_{p'}$ "corrected" to $\sup_{\pi'}$), and invent symbols (Grok's $H(X|Z,X',X,C)$ in Touchette and
Lloyd's Theorem 2). Agreement is therefore good evidence except against a correction both readers
would make. For spelling that residue was swept: every word of three or more
letters in every `latex` was looked up in the text layer of its pages (sources
with an unusable text layer excepted: Pauly, Klamka, Breuer, Peleg), and each
miss was a ligature or a line-break hyphen. A symbol both readers silently
"corrected" remains undetectable by comparison.

**Blindness.** Grok ran in a sandbox that mounted only the page images. Codex's
sandbox restricts writes, not reads, so its logs were checked: across all 668
runs the only command it executed was reading its own configuration file; it
opened no transcription, no other reader's output and no repository file.
