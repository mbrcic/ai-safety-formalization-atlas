/-
Vendored from `google-deepmind/debate` (Apache-2.0) via the Lean v4.31.0 port
`LukaHobor/debate` @ `dafe25d`. Changed at the header only; ledger and
rationale: `vendor/debate/PROVENANCE.md`.
-/

module

public import AISafetyAtlas.Upstream.Debate.Comp.Oracle
public import AISafetyAtlas.Upstream.Debate.Comp.Basic
public import AISafetyAtlas.Upstream.Debate.Comp.Defs
public import AISafetyAtlas.Upstream.Debate.Protocol
public import AISafetyAtlas.Upstream.Debate.Details
public import AISafetyAtlas.Upstream.Debate.Cost
public import AISafetyAtlas.Upstream.Debate.Correct
public import AISafetyAtlas.Upstream.Debate.Prob.Defs
public import AISafetyAtlas.Upstream.Debate.Prob.Pmf

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
Import definition and correctness proof for stochastic oracle debate
-/
