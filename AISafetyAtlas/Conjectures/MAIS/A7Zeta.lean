module

public import AISafetyAtlas.Conjectures.MAIS.O7Proof
public import AISafetyAtlas.Conjectures.MAIS.O77Chart

/-!
# `A7-ZETA-BRIDGE` — MAIS-A7's own definition of the local pair

`MAIS-A7.tex` `def:llc` does not define `(λ, m)` by a volume asymptotic. It
defines them by the zeta integral

    Z(z; w*, δ) = ∫_{B_δ(w*)} |L(w) − L(w*)|^z dw,

which resolution of singularities continues meromorphically to `ℂ`; `−λ` is its
largest pole and `m` that pole's order. The band-volume statement

    vol{w ∈ B_δ(w*) : |L(w) − L(w*)| < ε} ≍ ε^λ (log 1/ε)^(m−1)

appears immediately afterwards, introduced with the words *"In words:"* — a
gloss on the definition, outside the definition environment.

Every MAIS-O7 and MAIS-O77 theorem in this repository is about the gloss. The
substitution between the two was recorded in ledger prose and nowhere else,
while the identical substitution for `MAIS-A6`'s `def:local` was carried as
`O70-ZETA-BRIDGE`: a frozen proposition with consumers, stress artifacts and a
printed debt. This module removes that asymmetry. The gap is the same size it
was; it is now a hypothesis a reader can see in a binder rather than a sentence
they have to find.

## Why this is not `O70-ZETA-BRIDGE`

Neither half of that frontier reaches A7, and the second reason is the sharper.

*The germ is wrong.* `O70ZetaPoleBridge` speaks of `rrrLossCoords M N H C`
itself, because MAIS-O70's points are exact factorizations, where the loss
vanishes and the centred band germ **is** the loss. A7 quantifies over an
arbitrary point of the loss, and the object print integrates there is the
centred band `|L − L(w*)|`. Where `L(w*) ≠ 0` — which is every nonterminal
rung, `MAIS-O77(b)`'s whole subject — the centring is not removable, and
nothing about the loss alone says anything about that germ.

The two clauses this module serves sit on opposite sides of that line, so the
bridge is stated at the centred germ for both rather than case-split: `MAIS-O7`'s
terminal rung and `MAIS-O77(a)`'s fiber are exact factorizations, where the
centring collapses; `MAIS-O7`'s rank-zero rung and every point of `MAIS-O77(b)`
are saddles, where it does not.

*The antecedent is stronger than what is proved.* `O70ZetaPoleBridge` consumes
`HasExactLocalPair` — a ratio tending to `1`. MAIS-O7 and MAIS-O77(b) establish
`HasLocalVolumeOrder`, two-sided bounds only. Assuming the O70 bridge would
therefore not deliver the A7 rows even at the right germ, because they do not
supply its hypothesis. The bridge below is stated over what is actually proved.

## Why it is narrow

`ZetaPair.lean` records that the general proposition — for every nonnegative
germ the volume pair is the zeta pair — is **false**: a logarithmic correction
to the sublevel volume turns the pole into a branch point. What repairs it is
the hypothesis print carries, real-analyticity, and the reduced-rank loss is
polynomial in its coordinates, so it holds here. Stating the bridge at the germ
family it is used on rather than in general keeps the frontier at something that
could be true, which is the same rule `O70ZetaPoleBridge` follows.

`0 < lam` is print's own exclusion, in the form this interface can check: `def:llc`
requires `L` not identically `L(w*)` on any neighbourhood, "otherwise `Z` vanishes
identically and the invariants are undefined". A locally constant germ has
`HasLocalVolumeOrder` only in its degenerate branch, where `lam = 0`.

**Nothing here proves the bridge.** It is assumed, and every theorem that uses it
carries it in its binders.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.SingularLearning

/-- **`A7-ZETA-BRIDGE`.** Print's `def:llc`, at the germs A7 uses it on: for the
reduced-rank loss centred at an arbitrary point, a two-sided volume order is the
zeta pole order.

Assumed, not proved. -/
@[expose] public def A7ZetaVolumeBridge : Prop :=
  ∀ M N H : ℕ, 0 < M → 0 < N → 0 < H →
    ∀ (C : Matrix (Fin M) (Fin N) ℝ)
      (w : EuclideanSpace ℝ (Fin (H * N + M * H))) (lam : ℝ) (m : ℕ),
      0 < lam →
      HasLocalVolumeOrder (centeredBandGerm (rrrLossCoords M N H C) w) w lam m →
        HasZetaPoleOrder (centeredBandGerm (rrrLossCoords M N H C) w) w lam m

/-- **The frozen surface of `A7-ZETA-BRIDGE`.** Every quantifier written out and
both operational relations named, so the centring, the positivity of the
exponent and the direction of the implication are on the statement lock rather
than behind a definition. -/
public theorem a7ZetaVolumeBridge_iff :
    A7ZetaVolumeBridge ↔
      ∀ M N H : ℕ, 0 < M → 0 < N → 0 < H →
        ∀ (C : Matrix (Fin M) (Fin N) ℝ)
          (w : EuclideanSpace ℝ (Fin (H * N + M * H))) (lam : ℝ) (m : ℕ),
          0 < lam →
          HasLocalVolumeOrder
              (fun x => |rrrLossCoords M N H C x - rrrLossCoords M N H C w|) w lam m →
            HasZetaPoleOrder
              (fun x => |rrrLossCoords M N H C x - rrrLossCoords M N H C w|) w lam m :=
  Iff.rfl

/-! ## MAIS-O7 in print's own definition -/

/-- The scalar model's loss is the reduced-rank loss in coordinates, so the
bridge applies to it verbatim rather than by analogy. -/
public theorem o7Loss_eq_rrrLossCoords (s : ℝ) :
    o7Loss s = rrrLossCoords 1 1 2 (o7Target s) := rfl

/-- **The rank-zero rung has A7's zeta pair `(1,1)`**, conditional on the
bridge. -/
public theorem o7_zeta_pair_rankZero (hBridge : A7ZetaVolumeBridge) {s : ℝ}
    (hs : 0 < s) :
    HasZetaPoleOrder (centeredBandGerm (o7Loss s) 0) 0 1 1 := by
  rw [o7Loss_eq_rrrLossCoords]
  exact hBridge 1 1 2 one_pos one_pos (by norm_num) (o7Target s) 0 1 1 one_pos
    (by rw [← o7Loss_eq_rrrLossCoords]; exact hasLocalVolumeOrder_o7_origin hs)

/-- **Every point of the terminal rung has A7's zeta pair `(1/2, 1)`**,
conditional on the bridge. -/
public theorem o7_zeta_pair_terminal (hBridge : A7ZetaVolumeBridge) {s : ℝ}
    (hs : 0 < s) {w : O7Space} (hw : w ∈ o7TerminalRung s) :
    HasZetaPoleOrder (centeredBandGerm (o7Loss s) w) w (1 / 2) 1 := by
  rw [o7Loss_eq_rrrLossCoords]
  exact hBridge 1 1 2 one_pos one_pos (by norm_num) (o7Target s) w (1 / 2) 1
    (by norm_num)
    (by rw [← o7Loss_eq_rrrLossCoords]; exact hasLocalVolumeOrder_o7_terminal hs w hw)

/-- **MAIS-O7 is false in A7's own definition of the pair.**

The printed conjecture is `λ₀ < λ₁` along the saddle chain. At the scalar
instance the chain has two rungs; this gives both zeta-defined coefficients and
the failure of the printed inequality between them, for every positive target.

The content is the two pole orders. The final conjunct is arithmetic, and is
present so that the refutation is a single object rather than a comparison a
reader is asked to make. -/
public theorem o7_zeta_refutation (hBridge : A7ZetaVolumeBridge) {s : ℝ}
    (hs : 0 < s) :
    HasZetaPoleOrder (centeredBandGerm (o7Loss s) 0) 0 1 1 ∧
      (∀ w ∈ o7TerminalRung s,
        HasZetaPoleOrder (centeredBandGerm (o7Loss s) w) w (1 / 2) 1) ∧
      ¬ (1 : ℝ) < 1 / 2 :=
  ⟨o7_zeta_pair_rankZero hBridge hs,
    fun _w hw => o7_zeta_pair_terminal hBridge hs hw,
    by norm_num⟩

/-! ## MAIS-O77(a) in print's own definition

Part (a) is the one clause that needs **both** frontiers, and it is stated here
so that the exposure is legible rather than inferred: the volume-order table
already rests on `EigenvalueLawStatement`, and reading it as A7's pair adds
`A7ZetaVolumeBridge` on top.

`0 < lam` is print's own exclusion again, and here it is **derived** rather than
assumed: a factorization forces its rank stratum admissible, and `o70Lambda_pos`
makes the table value positive on every admissible stratum. So the theorem
quantifies over every exact factorization, with no side condition a caller has
to discharge. -/

/-- **MAIS-O77(a)'s table as A7's zeta pair**, at every exact factorization of
every certified target, conditional on both the Wishart eigenvalue law and the
zeta bridge. -/
public theorem o77_fiber_zeta_pair (hEigen : EigenvalueLawStatement)
    (hBridge : A7ZetaVolumeBridge) {M N H r : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hrH : r < H) (frame : O77SpectralFrame M N r)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (hBA : B * A = frame.target) :
    HasZetaPoleOrder
      (centeredBandGerm (o77LossCoords M N H frame.target) (matrixPairCoords A B))
      (matrixPairCoords A B)
      (((o77Pair M N H r A.rank B.rank).1 : ℚ) : ℝ)
      (o77Pair M N H r A.rank B.rank).2 := by
  have hH : 0 < H := Nat.lt_of_le_of_lt (Nat.zero_le r) hrH
  have hadm : AdmissibleRankData N M H r A.rank B.rank := by
    have h := admissible_of_mul_eq hN hM hH A B
    rw [hBA, frame.target_rank] at h
    exact h
  have hposQ : (0 : ℚ) < (o77Pair M N H r A.rank B.rank).1 := by
    simpa only [o77Pair, o70Pair] using o70Lambda_pos N M H r A.rank B.rank hadm
  have hpos : 0 < (((o77Pair M N H r A.rank B.rank).1 : ℚ) : ℝ) := by exact_mod_cast hposQ
  exact hBridge N M H hN hM hH frame.target (matrixPairCoords A B) _ _ hpos
    (isO77SourceFiberVolumeOrderTable_o77Pair hEigen M N H r hM hN hrH frame A B hBA).1

/-! ## MAIS-O77(b) in print's own definition -/

/-- A nonterminal rung forces both ambient dimensions positive, so the bridge's
non-degeneracy hypotheses are discharged rather than added: `k < r` makes the
target rank positive, and a rank bounds both sides of its shape. -/
public theorem pos_dims_of_rung {M N H r : ℕ} {frame : O77SpectralFrame M N r}
    {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) : 0 < M ∧ 0 < N := by
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le k) h.1
  have hM : r ≤ M := by
    have := frame.target.rank_le_card_width
    rw [frame.target_rank] at this
    simpa using this
  have hN : r ≤ N := by
    have := frame.target.rank_le_card_height
    rw [frame.target_rank] at this
    simpa using this
  exact ⟨lt_of_lt_of_le hr hM, lt_of_lt_of_le hr hN⟩

/-- **Every point of every nonterminal critical set has A7's zeta pair `(1,1)`**,
conditional on the bridge.

This is MAIS-O77(b) stated in the definition A7 prints, rather than in the gloss
that follows it. -/
public theorem o77_saddle_zeta_pair (hBridge : A7ZetaVolumeBridge)
    {M N H r : ℕ} {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (hrH : r < H) :
    HasZetaPoleOrder
      (centeredBandGerm (o77LossCoords M N H frame.target) (matrixPairCoords A B))
      (matrixPairCoords A B) 1 1 := by
  obtain ⟨hM, hN⟩ := pos_dims_of_rung h
  have hH : 0 < H := Nat.lt_of_le_of_lt (Nat.zero_le r) hrH
  exact hBridge N M H hN hM hH frame.target (matrixPairCoords A B) 1 1 one_pos
    (o77_saddle_two_sided_pair h hrH).1

/-- **MAIS-O77(b)'s all-saddle answer in A7's own definition**, at print's own
quantifiers and conditional only on the bridge. -/
public theorem o77_all_saddles_zeta_pair_one (hBridge : A7ZetaVolumeBridge) :
    ∀ M N H r : ℕ, r < H →
      ∀ (frame : O77SpectralFrame M N r) (k : ℕ)
        (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ),
        IsO77SaddleRungPoint frame k A B →
          HasZetaPoleOrder
            (centeredBandGerm (o77LossCoords M N H frame.target)
              (matrixPairCoords A B))
            (matrixPairCoords A B) 1 1 :=
  fun _M _N _H _r hrH _frame _k _A _B h => o77_saddle_zeta_pair hBridge h hrH

end AISafetyAtlas.Conjectures.MAIS
