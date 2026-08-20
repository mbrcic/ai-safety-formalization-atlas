/-
Vendored from `google-deepmind/debate` (Apache-2.0) via the Lean v4.31.0 port
`LukaHobor/debate` branch `port-lean-4.31`, revision `dafe25d`.

Changed by the atlas, mechanically and only at the file header: `module`, each
`import` rewritten to `public import` at the atlas module path, one
`@[expose] public section`, and the `set_option linter.*` block below. No
statement, proof script, notation, or declaration name in the body is altered.
Provenance and the full mapping: `vendor/debate/PROVENANCE.md`.
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

-- The atlas package builds with `warningAsError = true`; upstream does not.
-- Silencing the style linters keeps the vendored proof scripts identical to the
-- port rather than rewriting proofs to satisfy a policy they were not written
-- under. No correctness linter is touched, and incomplete proofs stay errors.
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
