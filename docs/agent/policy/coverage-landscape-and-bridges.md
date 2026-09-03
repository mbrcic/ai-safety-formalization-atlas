## Coverage, landscape, and bridges

- **Headline coverage:** reproduced registry formalizations with `EXACT` or
  `EQUIVALENT` only. `RELATED` does not increase the count.
- **Which record takes your edit:**
  | Where | Holds | Note |
  |---|---|---|
  | `registry.yaml` survey claim rows | what the Brcic–Yampolskiy survey asserted | `BY-001`…`BY-044` is **closed**; never add `BY-045` |
  | `registry.yaml` other claim rows | what any other source asserted | `CLM-` prefix; at least one `original_source_refs`; no survey-only fields (`paper_reference`, `survey_proof_assessment`, `formal_library_search`) |
  | `registry.yaml` artifact rows | formalizations standing on their own | `LAND-` prefix, no `informal_claim`, never headline coverage |
  | `conjectures.yaml` | every printed MAIS target: open questions, determine-problem specifications, and problems the atlas cannot state | `kind` says which; never a theorem, never counted as one |
  | `tasks.yaml` | the task board | `docs/guide/contributor-tasks.md` is **generated** — never edit the Markdown |
- **Sources are `directory` or `work`.** A directory is a curated map (the survey
  itself, `mathforaisafety.org`, AISI, MAIS): never graded against, entry count
  never a metric. A `work` is statement-bearing and is the only thing a
  statement-match grade may cite.
- **Claiming something does not exist?** That needs a `novelty_checks` record in
  `docs/provenance/formalization-search.json` — corpus, revision, date, and what
  the search did not cover. The six-corpus sweep is the `baseline-catalogue`
  profile for one source and is **not** inherited by new work.
- **Applications:** a declaration stated over an AI-system model may record a
  proposed `application` line — what it claims, over which model, and where the
  statement comes from. It is discovery prose, not review evidence; only a
  `REVIEWED` bridge supports a reviewed AI-system interpretation. Required on
  every `BRIDGE`. Generated view:
  [`docs/status/applications.md`](../../status/applications.md).
- **Layers:** (1) math theorem → (2) atlas interface → (3) AI-safety bridge →
  (4) real-system claim. Layers 3–4 need human review; Lean at 1–2 does not
  inherit an AI reading.
- **`ai_bridge_status`:** `HUMAN_REVIEW` → `STATEMENT_REVIEWED` → `REVIEWED`.
  Non-`HUMAN_REVIEW` needs a real `bridge_review` record under `docs/bridges/`.
  **Never invent** human review or graduate a bridge without authorization.
- Prefer `STATEMENT_REVIEWED` over overclaiming real systems.
- Robot (`action_safety_unverifiable`): **conditional reduction core**,
  relationship `RELATED`. Do not lengthen for paper show-off.
- GS: Isabelle `LAND-GS-001`; Lean facade `gibbard_satterthwaite` (`LAND-GS-002`).
  Do not vendor the rest of SocialChoiceLean without a consumer need.
