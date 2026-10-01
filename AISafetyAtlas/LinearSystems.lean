module

public import AISafetyAtlas.LinearSystems.MatrixLemmas
public import AISafetyAtlas.LinearSystems.Controllability
public import AISafetyAtlas.LinearSystems.Observability
public import AISafetyAtlas.LinearSystems.Hautus
public import AISafetyAtlas.LinearSystems.BlockBound
public import AISafetyAtlas.LinearSystems.Dynamics
public import AISafetyAtlas.LinearSystems.Flow

/-!
# State-space controllability and observability

The classical algebraic criteria for a finite-dimensional linear time-invariant
system `ẋ = A x + B u`, `y = C x`: the Kalman rank conditions and the Hautus
eigenvalue tests, with the duality that carries each observability statement to
its controllability counterpart.

**This layer was algebraic until 2026-09-20, and is not now.** The criteria are
still the heart of it, but `AISafetyAtlas.LinearSystems.Dynamics` and
`AISafetyAtlas.LinearSystems.Flow` define the differential equation, its
solutions and the output signal, and prove each criterion **equivalent** to the
property it was named for. The sentence this paragraph replaces said the
opposite — that nothing here defines a trajectory, a solution or an output
signal, and that *"the state cannot be reconstructed from the outputs"* is
therefore not proved. Both halves are now false, and the retraction is kept
rather than deleted.

| declaration | what it says |
|---|---|
| `IsObservable` | only the zero state is annihilated by every `C · Aᵏ`, `k < n` |
| `IsControllable` | every state is a combination of columns of `Aᵏ · B`, `k < n` |
| `isObservable_iff_observabilityMatrix_rank_eq` | Kalman: observable iff the stacked matrix has rank `n` |
| `isControllable_iff_controllabilityMatrix_rank_eq` | Kalman, controllability side |
| `unobservableSubspace` | the intersection of the kernels, `⊥` exactly when observable |
| `isObservable_iff_hautus` | Hautus: observable iff `[μI - A; C]` has trivial kernel for every `μ : ℂ` |
| `isControllable_iff_hautus` | Hautus, controllability side, by duality |
| `isControllable_iff_isObservable_transpose` | the duality itself |
| `IsTrajectoryOn`, `IsTrajectory` | `ẋ(t) = A x(t) + B u(t)`, asked on a set of times or everywhere |
| `outputSignal` | `y(t) = C x(t)` |
| `DeterminesStateOn` | the property: same input, same output on a window ⇒ same state there |
| `determinesStateOn_iff_isObservable` | that property **iff** the Kalman condition, on any non-empty open window |
| `IsCompletelyReachable` | the property: a run from any state to any state |
| `isCompletelyReachable_iff_isControllable` | that property **iff** the Kalman condition |
| `flow` | the matrix exponential `e^{At}`, with its group law and its derivative |
| `drivenState`, `drivenState_isTrajectory` | variation of constants: the run an input produces from rest |

**Provenance.** Four of the seven modules — `MatrixLemmas`, `Controllability`,
`Observability` and `Hautus` — are adapted from
[`AnandGokhale/LeanForControl`](https://github.com/AnandGokhale/LeanForControl)
at commit c5cedca, Apache-2.0; each file header carries the upstream file, its
SHA-256, and the atlas changes. Only the `LinearSystems` track was taken: the
rest of that development rests on seven custom axioms, including an assumed
Picard–Lindelöf, and would not pass this repository's axiom audit. `BlockBound`,
`Dynamics` and `Flow` are atlas-original and take nothing from it; the upstream
development has an analysis layer and a reachability file that are not connected
to each other, which is why building beat porting.

**Klamka.** `survey-ref-021` — Klamka, *Uncontrollability and unobservability of
multivariable systems*, IEEE TAC 17(5), 1972 — states *sufficient* conditions
through the minimal polynomial, and its own two properties are the dynamical
ones. Print's numbered results are in `BlockBound` at print's own quantities,
and print's two properties are in `Dynamics` and `Flow` with the equivalences
page 726 attributes to Chen and Desoer. Section 25 of
`docs/provenance/source-coverage-audit.md` grades the note statement by
statement; the triage is in
`docs/provenance/by001-by002-linear-systems-triage.md`.

Hautus is stated over `ℂ` because the eigenvalue argument needs an
algebraically closed field; the rank criteria are over an arbitrary field, and
the definitions over a semiring.
-/
