module

public import AISafetyAtlas.Upstream.Debate

/-!
# Doubly-efficient debate — public facade

A weak verifier decides a question it cannot answer itself by cross-examining two
stronger, untrusted debaters. Brown-Cohen, Irving and Piliouras
(*Scalable AI Safety via Doubly-Efficient Debate*, arXiv 2311.14125) prove that
the protocol is both **correct** — an honest debater wins against any opponent —
and **doubly efficient** — every party makes few oracle queries.

This is a **possibility** result, dual to the impossibility rows the rest of the
atlas carries: it says a form of scalable oversight provably works inside its
model. Landscape record `LAND-DEBATE-001`.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `Oracle` | A stochastic computation: bits drawn one at a time from the transcript so far |
| **Model** | `Lipschitz` | The final answer moves by at most `k ×` the oracle perturbation |
| **Model** | `Alice`, `Bob`, `Vera` | Prover, disprover, and the bounded verifier that adjudicates |
| **Model** | `protocol` | The `t`-round debate, as a query-counting computation |
| **Model** | `Params` | The parameter bundle the guarantees are proved against |
| **Model** | `defaultParams` | An inhabitant of that bundle for every `k > 0` and `t` |
| **Law** | `completeness` | Honest Alice reaches `true` with probability `≥ d`, against **any** Bob |
| **Law** | `soundness` | Honest Bob reaches `false` with probability `≥ d`, against **any** Alice |
| **Law** | `correctness` | Both at once, at the default parameters, with `w = 3/5 > 1/2` |
| **Bound** | `alice_fast` | Alice: `O(k² t log t)` queries, whatever Bob and Vera do |
| **Bound** | `bob_fast` | Bob: `O(k² t log t)` queries, whatever Alice and Vera do |
| **Bound** | `vera_fast` | Vera: `O(k²)` queries — independent of the number of rounds |

`vera_fast` is the reason the result is called *doubly* efficient: the trusted
party's work does not grow with the length of the argument it is checking.

## What this is not

The theorems below are statements about the protocol model, not about any
deployed oversight scheme. Four things upstream does **not** prove, carried here
unchanged:

* **Correctness only.** Space complexity is not formalized.
* **Time counts oracle queries only**, not full computational cost.
* The **Lipschitz oracle machine** is defined slightly differently from the
  paper — a stronger variant.
* Nothing here says a real debater can be trained to play the honest strategy,
  or that a real question factors into oracle bits.

No AI-system reading follows without a separate reviewed bridge
(the landscape row's `ai_bridge_status` is unreviewed).

## Why this module is not on the root import

The vendored development declares roughly 157 names in the **root** namespace —
`count`, `close`, `final`, `trace`, `estimate`, `step`, `L`, `Correct` among
them — so `import AISafetyAtlas` does not bring this facade in; import it on its
own, the contract `AISafetyAtlas.Explore` already keeps. Because the root
closure does not reach it, `scripts/check_print_axioms.py` audits it through an
explicit `OFF_ROOT_FACADES` list, and the six declarations below are pinned in
`docs/status/public-api.txt` like any other public name.

For the same reason `open AISafetyAtlas.Oversight.Debate` makes names such as
`Oracle` and `Alice` ambiguous against the upstream root declarations this module
re-exports. Import it and qualify — `open AISafetyAtlas.Oversight` and then
`Debate.Oracle` — as `AISafetyAtlas/Examples/Oversight/Debate.lean` does.

## Provenance

Upstream `google-deepmind/debate` (Apache-2.0), ported to Lean v4.31.0 and
vendored under `AISafetyAtlas/Upstream/Debate/`. Pins, statement fidelity and
every adaptation: `vendor/debate/PROVENANCE.md`. Reproduction evidence:
`docs/provenance/debate-reproduction.md`.
-/

namespace AISafetyAtlas.Oversight.Debate

noncomputable section

/-! ## The model -/

/-- A stochastic oracle: given the bits produced so far, a distribution over the
next bit. Upstream `Oracle`. -/
public abbrev Oracle := _root_.Oracle

/-- The three query budgets the protocol meters separately. Upstream `OracleId`,
whose constructors `AliceId`, `BobId` and `VeraId` are exported to the root
namespace. -/
public abbrev Party := _root_.OracleId

/-- `o` is `k`-Lipschitz over `t` rounds: perturbing the oracle by `ε` in the
supremum metric moves the probability of the final answer by at most `k * ε`.
Stated asymmetrically, as a neighbourhood of one particular oracle. Upstream
`Oracle.lipschitz`. -/
public abbrev Lipschitz (o : Oracle) (t : ℕ) (k : ℝ) : Prop :=
  _root_.Oracle.lipschitz o t k

/-- The distribution of the oracle's own answer after `t+1` steps — the ground
truth the debate is trying to reach. Upstream `Oracle.final`. -/
public abbrev finalAnswer (o : Oracle) (t : ℕ) : Prob Bool := _root_.Oracle.final o t

/-- The prover, arguing for `true`: given the transcript, a claimed probability
for the next bit. Upstream `Alice`. -/
public abbrev Alice := _root_.Alice

/-- The disprover, arguing for `false`: given the transcript and Alice's claim,
whether to challenge. Upstream `Bob`. -/
public abbrev Bob := _root_.Bob

/-- The bounded verifier, called only when Bob challenges. Same signature as
`Bob`, weaker parameters. Upstream `Vera`. -/
public abbrev Vera := _root_.Vera

/-- Honest Alice: estimate the true probability to within `e`, with failure
probability at most `q`. Upstream `alice`. -/
public abbrev honestAlice (e q : ℝ) : Alice := _root_.alice e q

/-- Honest Bob: challenge exactly when Alice's claim differs from his own
estimate by more than `(c+s)/2`. Upstream `bob`. -/
public abbrev honestBob (c s q : ℝ) : Bob := _root_.bob c s q

/-- The verifier: honest Bob's strategy at the verifier's weaker failure
probability. Upstream `vera`. -/
public abbrev verifier (s v q : ℝ) : Vera := _root_.vera s v q

/-- The `t`-round debate protocol, as a computation whose oracle queries are
counted per party. Upstream `debate`. -/
public abbrev protocol (alice : Alice) (bob : Bob) (vera : Vera) (t : ℕ) :
    Comp AllIds Bool :=
  _root_.debate alice bob vera t

/-- A parameter bundle valid for the guarantees: success probability `w`, output
probability `d`, Lipschitz constant `k`, round count `t`, together with the
inequalities relating the players' error and failure probabilities. Upstream
`Params`. -/
public abbrev Params (w d k : ℝ) (t : ℕ) := _root_.Params w d k t

/-- Default (untuned) parameters, exhibiting `Params (2/3) (3/5) k t` for every
positive `k` and every `t`. This is what keeps the guarantees below from being
statements about an empty hypothesis. Upstream `Params.defaults`. -/
public abbrev defaultParams (k : ℝ) (t : ℕ) (k0 : 0 < k) : Params (2/3) (3/5) k t :=
  _root_.Params.defaults k t k0

/-- The protocol is correct at success probability `w`: better than a coin, and
the honest player wins from either side. Upstream `Correct`. -/
public abbrev Correct (w k : ℝ) (t : ℕ) (alice : Alice) (bob : Bob) (vera : Vera) : Prop :=
  _root_.Correct w k t alice bob vera

/-! ## Correctness -/

/--
Completeness: if the oracle answers `true` with probability at least `w`, then
honest Alice drives the debate to output `true` with probability at least `d` —
against **any** Bob, including one that plays adversarially.

Upstream `completeness` (`AISafetyAtlas/Upstream/Debate/Correct.lean`), paper
Theorem 6.2.
-/
public theorem completeness {t : ℕ} {k w d : ℝ} (o : Oracle) (L : Lipschitz o t k)
    (eve : Bob) (p : Params w d k t) (m : w ≤ (finalAnswer o t).prob true) :
    d ≤ ((protocol (honestAlice p.c p.q) eve (verifier p.c p.s p.v) t).prob' o).prob true :=
  _root_.completeness o L eve p m

/--
Soundness: if the oracle answers `false` with probability at least `w`, then
honest Bob drives the debate to output `false` with probability at least `d` —
against **any** Alice.

Upstream `soundness` (`AISafetyAtlas/Upstream/Debate/Correct.lean`), paper
Theorem 6.2.
-/
public theorem soundness {t : ℕ} {k w d : ℝ} (o : Oracle) (L : Lipschitz o t k)
    (eve : Alice) (p : Params w d k t) (m : w ≤ (finalAnswer o t).prob false) :
    d ≤ ((protocol eve (honestBob p.s p.b p.q) (verifier p.c p.s p.v) t).prob' o).prob false :=
  _root_.soundness o L eve p m

/--
Correctness: at the default parameters the debate protocol is correct with
probability `3/5`, which is strictly better than a coin flip. Both directions
hold simultaneously for every positive Lipschitz constant and every round count.

Upstream `correctness` (`AISafetyAtlas/Upstream/Debate/Correct.lean`).
-/
public theorem correctness (k : ℝ) (k0 : 0 < k) (t : ℕ) :
    let p := defaultParams k t k0
    Correct (3/5) k t (honestAlice p.c p.q) (honestBob p.s p.b p.q)
      (verifier p.c p.s p.v) :=
  _root_.correctness k k0 t

/-! ## Query complexity

The bounds below are on **expected oracle queries**, not on total computational
cost, and they are unconditional in the opponents: each holds whatever the other
two parties do.
-/

/--
Alice makes `O(k² t log t)` expected queries at the default parameters,
regardless of Bob and Vera. Upstream `alice_fast`.
-/
public theorem alice_fast (o : Oracle) (k : ℝ) (k0 : 0 < k) (t : ℕ) (bob : Bob) (vera : Vera) :
    let p := defaultParams k t k0
    (protocol (honestAlice p.c p.q) bob vera t).cost' o AliceId ≤
      (t + 1) * (5000 * k ^ 2 * Real.log (200 * (t + 1)) + 1) :=
  _root_.alice_fast (o := o) k k0 t bob vera

/--
Bob makes `O(k² t log t)` expected queries at the default parameters, regardless
of Alice and Vera. Upstream `bob_fast`.
-/
public theorem bob_fast (o : Oracle) (k : ℝ) (k0 : 0 < k) (t : ℕ) (alice : Alice) (vera : Vera) :
    let p := defaultParams k t k0
    (protocol alice (honestBob p.s p.b p.q) vera t).cost' o BobId ≤
      (t + 1) * (20000 / 9 * k ^ 2 * Real.log (200 * (t + 1)) + 1) :=
  _root_.bob_fast (o := o) k k0 t alice vera

/--
Vera makes `O(k²)` expected queries at the default parameters — **independent of
`t`**, regardless of Alice and Bob. This is the "doubly" in doubly-efficient
debate: the trusted verifier's work does not grow with the length of the
argument being checked. Upstream `vera_fast`.
-/
public theorem vera_fast (o : Oracle) (k : ℝ) (k0 : 0 < k) (t : ℕ) (alice : Alice) (bob : Bob) :
    let p := defaultParams k t k0
    (protocol alice bob (verifier p.c p.s p.v) t).cost' o VeraId ≤ 106000 * k ^ 2 + 1 :=
  _root_.vera_fast (o := o) k k0 t alice bob

end

end AISafetyAtlas.Oversight.Debate
