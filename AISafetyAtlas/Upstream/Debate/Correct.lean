/-
Vendored from `google-deepmind/debate` (Apache-2.0) via the Lean v4.31.0 port
`LukaHobor/debate` @ `dafe25d`, and migrated in place to Lean v4.33.0. Changed at
the header only; ledger and rationale: `vendor/debate/PROVENANCE.md`.
-/

module

public import AISafetyAtlas.Upstream.Debate.Cost
public import AISafetyAtlas.Upstream.Debate.Details
public import AISafetyAtlas.Upstream.Debate.Protocol

@[expose] public section

-- Linters off per `vendor/debate/PROVENANCE.md`; no correctness linter is
-- touched and incomplete proofs stay errors.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

/-!
Correctness of the stochastic oracle doubly-efficient debate algorithm
-/

open Classical
open Prob
open scoped Real
noncomputable section

variable {t : ℕ} {k : ℝ}

/-- Completeness for any valid parameters -/
theorem completeness (o : Oracle) (L : o.lipschitz t k) (eve : Bob)
    {w d : ℝ} (p : Params w d k t) (m : w ≤ (o.final t).prob true) :
    d ≤ ((debate (alice p.c p.q) eve (vera p.c p.s p.v) t).prob' o).prob true :=
  completeness_p o L eve p m

/-- Soundness for any valid parameters -/
theorem soundness (o : Oracle) (L : o.lipschitz t k) (eve : Alice)
    {w d : ℝ} (p : Params w d k t) (m : w ≤ (o.final t).prob false) :
    d ≤ ((debate eve (bob p.s p.b p.q) (vera p.c p.s p.v) t).prob' o).prob false :=
  soundness_p o L eve p m

/-- The debate protocol is correct with probability 3/5, using the default parameters -/
theorem correctness (k : ℝ) (k0 : 0 < k) (t : ℕ) :
    let p := Params.defaults k t k0
    Correct (3/5) k t (alice p.c p.q) (bob p.s p.b p.q) (vera p.c p.s p.v) where
  half_lt_w := by norm_num
  complete o eve L m := completeness o L eve (.defaults k t k0) m
  sound o eve L m := soundness o L eve (.defaults k t k0) m
