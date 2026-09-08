module

public import AISafetyAtlas.Conjectures.MAIS.A7Zeta
public import AISafetyAtlas.Examples.Conjectures.MAIS.O77Chart

/-!
# Worked models for `A7-ZETA-BRIDGE`

The bridge is assumed, so nothing here is an inhabitant of it. What these
witness is that its consumers are not vacuous: each names a point that exists,
at which the volume-order hypothesis the bridge consumes is proved
unconditionally elsewhere in the tree.

That distinction is the whole reason this file exists. A conditional theorem
whose antecedent is never satisfiable is as green as one whose antecedent holds
everywhere, and the difference is invisible to the build.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.SingularLearning
open AISafetyAtlas.Conjectures.MAIS

/-- **MAIS-O7 refuted in A7's zeta definition**, at the scalar target `s = 1`. -/
example (hBridge : A7ZetaVolumeBridge) :
    HasZetaPoleOrder (centeredBandGerm (o7Loss 1) 0) 0 1 1 ∧
      (∀ w ∈ o7TerminalRung 1,
        HasZetaPoleOrder (centeredBandGerm (o7Loss 1) w) w (1 / 2) 1) ∧
      ¬ (1 : ℝ) < 1 / 2 :=
  o7_zeta_refutation hBridge one_pos

/-- **A7's zeta pair at a rung that is not the rank-zero one.**

`rank2Frame` is the `2 x 2` target with distinct singular values `a > b > 0`,
and `rungPoint_rank2` places a point on its `k = 1` rung, where the truncation
is nonzero and neither factor vanishes. So the zeta reading is exercised where
the underlying volume argument runs its whole course, not only where the
spectral step is trivially true. -/
example (hBridge : A7ZetaVolumeBridge) (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    HasZetaPoleOrder
      (centeredBandGerm (o77LossCoords 2 2 3 (rank2Frame a b hb hab).target)
        (matrixPairCoords (rank2A a) rank2B))
      (matrixPairCoords (rank2A a) rank2B) 1 1 :=
  o77_saddle_zeta_pair hBridge (rungPoint_rank2 a b hb hab) (by norm_num)

/-- The all-saddle form, instantiated at that same rung. -/
example (hBridge : A7ZetaVolumeBridge) (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    HasZetaPoleOrder
      (centeredBandGerm (o77LossCoords 2 2 3 (rank2Frame a b hb hab).target)
        (matrixPairCoords (rank2A a) rank2B))
      (matrixPairCoords (rank2A a) rank2B) 1 1 :=
  o77_all_saddles_zeta_pair_one hBridge 2 2 3 2 (by norm_num)
    (rank2Frame a b hb hab) 1 (rank2A a) rank2B (rungPoint_rank2 a b hb hab)

/-- **The dimensions are derived, not assumed.** A nonterminal rung forces both
ambient dimensions positive, which is what lets `o77_saddle_zeta_pair` discharge
the bridge's non-degeneracy hypotheses instead of taking them. -/
example (a b : ℝ) (hb : 0 < b) (hab : b < a) : 0 < 2 ∧ 0 < 2 :=
  pos_dims_of_rung (rungPoint_rank2 a b hb hab)

end AISafetyAtlas.Examples.Conjectures.MAIS
