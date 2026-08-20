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

public import Mathlib.Topology.MetricSpace.Basic
public import AISafetyAtlas.Upstream.Debate.Prob.Defs
public import Mathlib.Data.Vector.Basic

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
Stochastic oracle as a model of general, randomized computations

We formalize debate w.r.t. randomized computations allowed to query a stochastic oracle.
For simplicity, we embed all details of the computation as the oracle, including deterministic
features.  Concretely, we start with zero bits, and repeatedly prepend bits from the oracle
for some number of steps.  The final bit is the result.
-/

open Classical
open Prob
open Option (some none)
open scoped Real
noncomputable section

/-- A stochastic oracle -/
def Oracle := (n : ℕ) → List.Vector Bool n → Prob Bool

/-- n random bits from an oracle, each given by feeding the oracle the previous result.
    This models an arbitrary computation, as o can behave differently based on input length. -/
def Oracle.fold (o : Oracle) : (n : ℕ) → Prob (List.Vector Bool n)
| 0 => pure List.Vector.nil
| n+1 => do
  let y ← o.fold n
  let x ← o _ y
  return y.cons x

/-- The (n+1)th bit of o.fold -/
def Oracle.final (o : Oracle) (t : ℕ) : Prob Bool := do
  let x ← o.fold (t+1)
  return x.head

/-- The distance between two oracles is the sup of their probability differences -/
instance : Dist Oracle where
  dist o0 o1 := ⨆ n, ⨆ y : List.Vector Bool n, |(o0 _ y).prob true - (o1 _ y).prob true|

/-- An oracle computation is k-Lipschitz if the final probability differs by ≤ k * oracle dist.
    We define this asymmetrically, as we want the neighborhood of a particular oracle. -/
structure Oracle.lipschitz (o : Oracle) (t : ℕ) (k : ℝ) : Prop where
  k0 : 0 ≤ k
  le : ∀ o' : Oracle, |(o.final t).prob true - (o'.final t).prob true| ≤ k * dist o o'
