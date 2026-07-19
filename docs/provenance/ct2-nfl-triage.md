# CT-2 — Triage of AFP `No_Free_Lunch_ML` for BY-020 / BY-021

Statement-level triage of the AFP candidate `No_Free_Lunch_ML` against the
survey's No-Free-Lunch rows. Draft classification; reproduction log appended
once the pinned session build completes.

## Upstream candidate (pinned)

- Upstream: [AFP — No-free-lunch theorem for machine learning](https://www.isa-afp.org/entries/No_Free_Lunch_ML.html)
- Release: `2026-02-06`, compatible Isabelle2025-2
- Archive SHA-256: `93ce8953bac6b09a29f6d2aafa64d4dbedf49e11f13cdad4cddc42f95f173588`
- Session: `No_Free_Lunch_ML` (depends only on `HOL-Probability`; no external AFP deps)
- Theory: `No_Free_Lunch_ML.thy`
- Principal declaration: `theorem no_free_lunch_ML`
- Reproduce: `scripts/reproduce_isabelle.sh nfl`

## What the entry actually proves

The abstract and `theorem no_free_lunch_ML` state the **statistical-learning /
PAC** no-free-lunch theorem, explicitly *"following Section 5.1 of Shalev-Shwartz
& Ben-David, Understanding Machine Learning"* (their Theorem 5.1).

Informal reading of the pinned statement: for binary classification over a
finite domain `X` with `2 * m < |X|`, for **every** learner
`A : (sample of size m) → (X → bool)` there **exists** a distribution `𝒟` on
`X × bool` such that

- `𝒟` is realizable — some `f` achieves loss `0` (`P[(x,y)∼𝒟. f x ≠ y] = 0`), and
- the learner fails with constant probability:
  `P[S∼𝒟^m. L_𝒟(A(S)) > 1/8] ≥ 1/7`.

Proof technique: average the learner's error over a finite family of
label functions on a `2m`-sized domain slice, then Markov's inequality
(`prob_space.Markov_inequality_measure_minus` is the supporting lemma).

## Per-row classification

| Row | Survey theorem | Relationship | Verdict |
|-----|----------------|--------------|---------|
| BY-020 | Wolpert 1996, *A Priori Distinctions Between Learning Algorithms* (supervised NFL) | Both assert "no universal learner," but Wolpert's is a **uniform average of off-training-set error over all target functions** (a symmetry/counting identity); the AFP entry is a **sample-complexity adversarial lower bound** (SSBD Thm 5.1) with a domain-size hypothesis `2m < |X|`, realizability, and explicit `1/8`, `1/7` constants. Different statement, hypotheses, and proof. | **DISTINCT** — related concept, not coverage |
| BY-021 | Wolpert–Macready 1997, *No Free Lunch Theorems for Optimization* | The AFP entry is about **classification learning**, not black-box optimization over an objective landscape. No shared formal object. | **DISTINCT** — not coverage |
| BY-022 | Auger–Teytaud continuous / Wolpert–Macready coevolutionary free lunches | Unrelated (continuous-space / coevolution *free-lunch* results). | **DISTINCT** — not coverage |

**Net:** the AFP candidate covers **none** of BY-020 / BY-021 / BY-022. The
prior "candidate (pending CT-2)" tag on BY-020 and BY-021 was a keyword match
(`no free lunch`), not a statement match — it should be **removed**, and the
rows return to *no known formalization*.

## Recommendation

1. **Downgrade** BY-020 and BY-021 candidate evidence: drop `No_Free_Lunch_ML`
   from their `candidate_formalizations`; note it is a distinct (SSBD)
   theorem, not the Wolpert results.
2. **Add a new survey row** for the Shalev-Shwartz–Ben-David statistical-learning
   NFL (Understanding ML §5.1 / Thm 5.1) which the AFP entry **does** formalize.
   Classify as reproduced Isabelle coverage once the build log below lands —
   this is a genuine, correctly-attributed formalized learning-theory limitation
   for the atlas.
3. Keep the Wolpert supervised/optimization NFL rows as *unformalized* — the
   boosting-list "easy win" claim still stands for those specific statements.

## AI-safety relevance

Recorded as substrate, not a safety-specific theorem (hence landscape, not a BY
coverage row). Its value for AI safety is sharper and less contested than the
uniform-averaging Wolpert NFL:

- **Inductive bias is necessary, not optional.** With `2*m < |X|` there is no
  distribution-free guarantee: data alone cannot yield a safe learner without
  restricting the hypothesis class. This is formal backing for "safety must come
  from specification / structural assumptions, not more data."
- **A worst-case distribution always exists.** For *every* learner some
  realizable distribution drives `P[L(A(S)) > 1/8] >= 1/7` — a quantitative
  out-of-distribution / distribution-shift failure statement, not an asymptotic
  one. Even when a perfect (loss-0) predictor exists, bounded-sample learning can
  miss it.
- **No uniform-prior premise.** Unlike Wolpert's NFL, it does not assume a
  uniform prior over all target functions, so the "learning has limits" argument
  is harder to dismiss as an artifact of the averaging measure.

Scope limit: binary classification with domain large relative to sample size;
silent once the hypothesis class is restricted or samples suffice — which is the
point, since safety is exactly that restriction. Wolpert NFL (BY-020/BY-021)
remains the survey's slogan-level result and is still unformalized.

## Reproduction status — reproduced (2026-07-19)

Built with the pinned `makarius/isabelle` image against the SHA-256-checked
`afp-No_Free_Lunch_ML-2026-02-06.tar.gz`
(`93ce8953bac6b09a29f6d2aafa64d4dbedf49e11f13cdad4cddc42f95f173588`) via
`scripts/reproduce_isabelle.sh nfl`. Session depends only on `HOL-Probability`.

```text
Finished HOL-Probability (0:00:46 elapsed time, 0:03:05 cpu time, factor 4.00)
Running No_Free_Lunch_ML ...
No_Free_Lunch_ML: theory No_Free_Lunch_ML.No_Free_Lunch_ML 100% (4.604s cumulated time)
Finished No_Free_Lunch_ML (0:00:04 elapsed time, 0:00:06 cpu time, factor 1.35)
```

Build exit code `0`; `theorem no_free_lunch_ML` checks. This reproduces the SSBD
formalization (landscape row `LAND-NFL-001`); it does **not** reproduce or cover
BY-020 / BY-021, which remain unformalized.
