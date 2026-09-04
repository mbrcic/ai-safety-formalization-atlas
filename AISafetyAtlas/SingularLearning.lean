module

public import AISafetyAtlas.SingularLearning.AoyagiWatanabe
public import AISafetyAtlas.SingularLearning.DyadicLocalization
public import AISafetyAtlas.SingularLearning.EliminationChart
public import AISafetyAtlas.SingularLearning.ChartTransport
public import AISafetyAtlas.SingularLearning.ChartAnalytic
public import AISafetyAtlas.SingularLearning.ChartAssembly
public import AISafetyAtlas.SingularLearning.TauberianLog
public import AISafetyAtlas.SingularLearning.LayerCake
public import AISafetyAtlas.SingularLearning.EigenvalueLaw
public import AISafetyAtlas.SingularLearning.ResidualGerm
public import AISafetyAtlas.SingularLearning.ResidualLaplace
public import AISafetyAtlas.SingularLearning.ResidualScalar
public import AISafetyAtlas.SingularLearning.ChartCoords
public import AISafetyAtlas.SingularLearning.ChartGerm
public import AISafetyAtlas.SingularLearning.CoordTransfer
public import AISafetyAtlas.SingularLearning.DiffeoTransfer
public import AISafetyAtlas.SingularLearning.OrbitTransport
public import AISafetyAtlas.SingularLearning.StratumTransport
public import AISafetyAtlas.SingularLearning.JacobianSandwich
public import AISafetyAtlas.SingularLearning.GaussianQuadratic
public import AISafetyAtlas.SingularLearning.GramSpectrum
public import AISafetyAtlas.SingularLearning.LaplaceScale
public import AISafetyAtlas.SingularLearning.LocalPair
public import AISafetyAtlas.SingularLearning.ZetaPair
public import AISafetyAtlas.SingularLearning.ZetaMonomial
public import AISafetyAtlas.SingularLearning.LossAnalytic
public import AISafetyAtlas.SingularLearning.PairTransfer
public import AISafetyAtlas.SingularLearning.ChamberIntegral
public import AISafetyAtlas.SingularLearning.MatrixAnalytic
public import AISafetyAtlas.SingularLearning.MatrixNormBridge
public import AISafetyAtlas.SingularLearning.Coordinates
public import AISafetyAtlas.SingularLearning.Loss
public import AISafetyAtlas.SingularLearning.OrbitNormalForm
public import AISafetyAtlas.SingularLearning.RankRealization
public import AISafetyAtlas.SingularLearning.ReducedRank
public import AISafetyAtlas.SingularLearning.Tauberian

/-!
# Singular learning theory: the reduced-rank template

**This module declares nothing.** It is the aggregate import of the
singular-learning layer, kept so import paths resolve as the layer grows.

`AoyagiWatanabe` is the transcription of `MAIS-A6.tex` Theorem `thm:aw` — the
four-case global learning coefficient and multiplicity of reduced-rank
regression — together with the rank-feasibility vocabulary that MAIS-O70's
statement layer consumes. On top of it the layer now carries the local pair of
an actual loss germ:

* the local pair and its transfer calculus — `LocalPair`, `ZetaPair`, `PairTransfer`,
  `DiffeoTransfer`, `CoordTransfer`, `JacobianSandwich`, `OrbitTransport`,
  `StratumTransport`;
* the elimination chart — `EliminationChart`, `ChartTransport`, `ChartAnalytic`,
  `ChartAssembly`, `ChartCoords`, `ChartGerm`;
* the Laplace and Tauberian bridge — `LaplaceScale`, `GaussianQuadratic`,
  `LayerCake`, `DyadicLocalization`, `Tauberian`, `TauberianLog`, `ResidualGerm`,
  `ResidualLaplace`, `ResidualScalar`;
* the chamber calculus — `ChamberIntegral`, `GramSpectrum`, `EigenvalueLaw`.

Two things are still **not** here. The agreement of the two normalizations of the
local pair: `ZetaPair` does state the zeta function `zetaIntegral`, print's
primary pole-order reading `HasZetaPoleOrder`, and the weaker real-axis bound
`HasZetaRealAxisOrder` that the candidate proves for a sharp ball — but every
result the atlas proves is proved about the ball-volume form, and the bridge
between the two, `O70ZetaPoleBridge`, is what `MAIS-A6.tex` `def:local` asserts
with its "Equivalently" and what the atlas states as a hypothesis and proves
nowhere. And `EigenvalueLaw`'s `EigenvalueLawStatement` is a
hypothesis, not a theorem — everything downstream of it carries it as a visible
binder.

One germ of the family does not need the hypothesis at all. `ResidualScalar` proves the local
pair of `residualGerm 1 1 1`, that is `x²y²`, unconditionally: the reduction
`gaussianLaplace_residualGerm_eq_det` carries no frontier, at `1×1` the determinant integral is
a single one-dimensional integral, and an elementary split at `|x| = T^{-1/2}` brackets it
between two multiples of `T^{-1/2} log T`. That is the first *singular* germ in the atlas with
an unconditional local pair.

`awLambda` remains *transcribed arithmetic*; that it is the global learning
coefficient of the model is Aoyagi–Watanabe's theorem, and it is not formalized
in the atlas.
-/
