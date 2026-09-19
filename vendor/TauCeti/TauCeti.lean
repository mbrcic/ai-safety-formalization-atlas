module

public import TauCeti.Analysis.Calculus.Bilinear
public import TauCeti.Analysis.Calculus.Hadamard
public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Calculus.Morse.NormalForm
public import TauCeti.Analysis.Calculus.ParametricIntegral
public import TauCeti.Analysis.Calculus.SecondDerivative
public import TauCeti.Analysis.Normed.Algebra.SquareRoot
public import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Vendored Tau Ceti modules

The eight modules of `TauCetiProject/TauCeti` that carry the Morse lemma in a
Banach space and its dependency cone. See `PROVENANCE.md` in this directory for
the upstream pin, the two backport edits, and the statement-fidelity audit.

Nothing in the atlas imports this root; a consuming module imports the leaf it
needs. The root exists so that `lake build TauCeti` covers the tree and CI
notices when a Mathlib bump breaks it.
-/
