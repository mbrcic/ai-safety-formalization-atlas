# Printed statements, transcribed from the page

The source's own statement for every printed claim the atlas grades, in LaTeX,
transcribed from an image of the pinned PDF page. This is what a scope or coverage
grade compares the Lean against: not the atlas's paraphrase in
`source-coverage-audit.md`, and not text pulled from the PDF's text layer.

## Why from the page image

The text layer cannot be trusted for this. Measured on the 315 graded rows
(2026-11-14, `regrade-2026-11/`): in two-column layouts `pdftotext -layout` splices
the neighbouring column into the middle of a sentence; displayed formulas lose
symbols the font does not map (`≠` extracted as `=`, glyphs dropped entirely); and
reading-order extraction, which fixes the columns, moves displayed formulas out of
the sentence (it dropped "If X → Y → Z, then" from Cover & Thomas Theorem 2.8.1).
158 of 315 rows were affected in one of these ways. A transcription read off the
rendered page has none of these failure modes, and it is checked by a second reader
against the same image.

## Layout

One YAML file per source (or per chapter of a long book), named after the source.
Each file:

```yaml
source:
  citation: <full citation, the edition the audit cites>
  file: <file name in the pinned literature directory>
  sha256: <hash of that file; must match the audit's pin>
  page_offset: <PDF page minus printed page, where constant>
  standing: <the source's standing assumptions for these statements, LaTeX, with page>
definitions:            # every definition a statement below uses, written once
  - id: <slug>
    label: <e.g. "Definition (mutual information)">
    pdf_page: <n or n-m>
    book_page: <n or n-m>
    latex: |
      <the definition as printed, with the conventions printed alongside it
       (e.g. 0 log 0 = 0); `[\ldots]` marks an omission>
    transcribed: {...}
    checked: {...}
statements:
  - id: <short stable key: source slug + the source's own label>
    audit_row: <row id in regrade-2026-11, e.g. S01-R05>
    locator: <the locator the audit uses>
    pdf_page: <n>
    book_page: <n>
    label: <the source's label, e.g. "Theorem 2.8.1", or "remark">
    latex: |
      <the statement exactly as printed: wording, symbols, equation numbers;
       emphasis kept with \emph; nothing added, nothing corrected>
    grades: <optional: only when the printed text holds more than this row grades
             (one sentence split across rows): the part this row grades>
    context: |
      <optional: only where the statement cannot be read without it, e.g. the
       sentence that introduces a bulleted consequence>
    uses: [<definition or statement ids whose meaning the statement depends on>]
    proof_pages: <PDF pages of the source's proof, if it has one; not transcribed>
    note: <optional: a slip, an ambiguity, or a reading the grader needs flagged>
    transcribed: {by: <who>, date: <YYYY-MM-DD>, from: page image, dpi: <n>}
    checked: {by: <who>, date: <YYYY-MM-DD>}   # second reader, same image
excerpts:               # proof passages, only where a grading decision rests on one
  - id: <slug>
    for: [<statement ids>]
    reason: <the decision it supports: a slip repair, a hidden hypothesis the
             proof uses, a derivation step cited as visible>
    pdf_page: <n>
    latex: |
      <the passage as printed, as short as the reason allows>
    transcribed: {...}
    checked: {...}
```

Rules:

- **Verbatim.** Transcribe what is printed, including a slip. A repair is never
  made here; it goes in `note`, and the grading of repairs follows the ruling in
  `regrade-2026-11/RULINGS-PENDING.md` (refute the literal print first).
- **Nothing editorial inside `latex`.** The only insertion allowed is `[\ldots]`
  for omitted text; pages, joins between passages and comments go in `note`. A
  diagram is drawn (e.g. with `array`), never described in words.
- **Whole statement.** Hypotheses printed with the statement are part of `latex`.
  Standing assumptions of the section go in `source.standing`, each with its page.
- **Definitions, not proofs.** Every term a statement uses is transcribed once
  under `definitions`; a scope grade depends on what the terms mean. Proofs are
  located (`proof_pages`) but not transcribed, except as short `excerpts` where a
  grading decision rests on the passage: a slip repair, a hypothesis the proof uses
  that the statement leaves out, or a step cited as a visible derivation. Grading
  compares the Lean with the statement; reading the source's proof audits the
  source, not the Lean. (Whole proofs would also be copying copyrighted text.)
- **Page images are not committed** (the sources are copyrighted). Rebuild one with
  `pdftoppm -r 130 -f <pdf_page> -l <pdf_page> -png <file> out`.
- **`checked` is required** before a file is used for grading.

Notes that cite a *source card* (`S01`-`S28`) or `source-cards/map.tsv` refer to the grader's per-source
working notes from the 2026-11 regrade. They are not published; the transcriptions in this folder supersede
their quotations (see `FINDINGS.md`).
