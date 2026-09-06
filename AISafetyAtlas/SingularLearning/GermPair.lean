module

public import AISafetyAtlas.SingularLearning.SylvesterPair
public import AISafetyAtlas.SingularLearning.FreeBlockPair

/-!
# An arbitrary indefinite form plus a free-block germ

Two modules each hold half of what print's two-sided band lemma asks for.

* `hasLocalVolumeOrder_freeBlockGerm` proves the `Θ(ε)` band order
  for `|Q(ξ) + g(ζ)|` with a continuous germ `g` on a free block, but only when
  the quadratic part is literally `modelBandForm p q`, the model signature form.
* `hasLocalVolumeOrder_abs_matrixQuadForm` handles an arbitrary
  nondegenerate indefinite matrix form, but with no germ: the absolute value is
  taken of the quadratic part alone.

Neither is enough on its own.  A caller who holds an arbitrary `K` *and* a germ
cannot reach the first, because its statement names the model form; and cannot
reach the second, because the germ is added inside the absolute value, so the
transport `hasLocalVolumeOrder_abs_of_congruent` performs — which only ever sees
`|Q|` — has nothing to say about `|Q + g|`.

What joins them is a **signed** congruence.  `hasLocalVolumeOrder_abs_of_diagonal`
already builds the linear equivalence carrying a diagonalised form to the model,
and then discards it, keeping only the identity between absolute values.  Kept
signed, the same equivalence carries `Q(ξ) + g(ζ)` to `modelBandForm p q (e ξ) +
g(ζ)`, which is exactly `freeBlockGerm`, and the free block is untouched because
the equivalence is the identity there.

## Why the congruence is a disjunction

`exists_model_congruence` concludes

    `Q = modelBandForm p q ∘ e`   **or**   `Q = -(modelBandForm p q ∘ e)`,

with `2 ≤ p` in both branches, and the disjunction is not slack in the proof: the
one-sided statement is false.  Sylvester's law of inertia makes the signature an
invariant of a form under linear congruence, so `Q = modelBandForm p q ∘ e`
forces `(p, q)` to *be* the signature of `Q`.  At `K = diag(1,-1,-1,-1)` that
signature is `(1, 3)`, and no congruence to a model form with `2 ≤ p` exists.
Negating the form exchanges the blocks, which is why the second branch always
applies when the first cannot: `-Q` has signature `(3, 1)` there.

That last paragraph is an argument in prose, not a checked declaration: the tree
does not carry the inertia-invariance theorem in the form "no such `e` exists",
so the disjunction is *not* accompanied by a Lean proof that it cannot be
narrowed.  What is checked is that the disjunctive statement is provable and that
its second branch is the one an explicit signature-`(1,3)` matrix takes —
`Examples.SingularLearning.GermPair.hasLocalVolumeOrder_negMinkowski4_add_evenGerm`.

The `2 ≤ p` is what the band estimate needs and is where `3 ≤ n` is spent — both
blocks are nonempty because the form takes both signs, and three indices split
between two nonempty blocks put at least two in one of them.

## What the sign costs downstream

Nothing.  `|(-Q) + (-g)| = |Q + g|`, and `-g` is continuous and vanishes at the
origin whenever `g` does, so the negative branch of `exists_model_congruence` is
absorbed by running the same argument at `-g`.  The germ hypotheses are stable
under negation, which is the only reason the disjunction is harmless here; a
statement whose germ hypotheses were one-sided would have to carry the branch.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory
open scoped Matrix

/-! ## The signed congruence

`hasLocalVolumeOrder_abs_of_diagonal` builds the coordinate change and keeps only
`|Q x| = modelBandGerm p q (e x)`.  These two lemmas keep the signed identity
`Q x = modelBandForm p q (e x)` instead, which is what survives adding a germ.
-/

/-- **The coordinate change behind `hasLocalVolumeOrder_abs_of_diagonal`, kept
signed.**  A form presented as a `±1`-weighted sum of squares with its signs
already sorted by `τ` is carried by an explicit linear equivalence to the model
form of signature `(p, q)` — not merely to its absolute value.

The equivalence is the same `(f ≫ sortProd τ) ≫ splitLE p q` that module builds;
only the conclusion differs, and it differs in exactly the way a caller adding a
germ needs. -/
public theorem exists_signed_congruence_of_diagonal {n p q : ℕ} (hpq : p + q = n)
    {Q : EuclideanSpace ℝ (Fin n) → ℝ}
    (w : Fin n → ℝ) (f : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ))
    (τ : Fin p ⊕ Fin q ≃ Fin n)
    (hpos : ∀ a : Fin p, w (τ (Sum.inl a)) = 1)
    (hneg : ∀ b : Fin q, w (τ (Sum.inr b)) = -1)
    (hQ : ∀ x, Q x = ∑ i, w i * (f x i * f x i)) :
    ∃ e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q)),
      ∀ x, Q x = modelBandForm p q (e x) := by
  subst hpq
  refine ⟨((f.trans (sortProd τ)).trans (splitLE p q)).toContinuousLinearEquiv, fun x => ?_⟩
  have hcoe : (((f.trans (sortProd τ)).trans (splitLE p q)).toContinuousLinearEquiv : _ → _) x
      = splitLE p q (sortProd τ (f x)) := rfl
  rw [hcoe]
  rcases hsp : sortProd τ (f x) with ⟨u, v⟩
  have hu : ‖u‖ ^ 2 = ∑ a : Fin p, (f x (τ (Sum.inl a))) ^ 2 := by
    rw [← norm_sq_sortProd_fst τ (f x), hsp]
  have hv : ‖v‖ ^ 2 = ∑ b : Fin q, (f x (τ (Sum.inr b))) ^ 2 := by
    rw [← norm_sq_sortProd_snd τ (f x), hsp]
  rw [modelBandForm_splitLE, hu, hv, hQ x, sum_weighted_sq_eq_split w τ hpos hneg (f x)]

/-- **A nondegenerate indefinite matrix form is congruent to a model form with a
two-dimensional first block, up to sign.**

The weight vector, the coordinates and the sign-sorting bijection are produced
here from `K` alone, exactly as in `hasLocalVolumeOrder_abs_matrixQuadForm`; what
is new is that the identity is kept signed and that the first block is made the
larger one.

Which disjunct holds is decided by the inertia of `K`: the first when `K` has at
least two positive squares, the second when it has at most one, in which case
`3 ≤ n` and nondegeneracy leave at least two negative squares and the roles of
the blocks are exchanged.  A one-sided conclusion is unprovable — see the module
header. -/
public theorem exists_model_congruence {n : ℕ} (h3 : 3 ≤ n)
    (K : Matrix (Fin n) (Fin n) ℝ) (hsymm : K.IsSymm) (hdet : K.det ≠ 0)
    (hpos : ∃ z, 0 < matrixQuadForm K z) (hneg : ∃ z, matrixQuadForm K z < 0) :
    ∃ (p q : ℕ) (_ : 2 ≤ p) (_ : NeZero q) (_ : p + q = n)
      (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q))),
      (∀ z, matrixQuadForm K z = modelBandForm p q (e z))
        ∨ (∀ z, matrixQuadForm K z = -modelBandForm p q (e z)) := by
  classical
  obtain ⟨w, g, hw, hgQ⟩ :=
    exists_diagonal_coords (M := Fin n → ℝ) (Module.finrank_fin_fun ℝ)
      (Matrix.toQuadraticForm' K) (separatingLeft_of_det_ne_zero K hsymm hdet)
  set f : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans g with hf
  have hQ : ∀ z, matrixQuadForm K z = ∑ i, w i * (f z i * f z i) := by
    intro z
    rw [matrixQuadForm_eq K z, hgQ]
    rfl
  obtain ⟨p, q, hpq, τ, hp1, hq1⟩ := exists_sign_split w hw
  have hsplit : ∀ z, matrixQuadForm K z
      = (∑ a : Fin p, (f z (τ (Sum.inl a))) ^ 2)
        - ∑ b : Fin q, (f z (τ (Sum.inr b))) ^ 2 := by
    intro z
    rw [hQ z, sum_weighted_sq_eq_split w τ hp1 hq1 (f z)]
  have hpne : p ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := hpos
    rw [hsplit z] at hz
    have hnn : (0:ℝ) ≤ ∑ b : Fin q, (f z (τ (Sum.inr b))) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_sub] at hz
    linarith
  have hqne : q ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := hneg
    rw [hsplit z] at hz
    have hnn : (0:ℝ) ≤ ∑ a : Fin p, (f z (τ (Sum.inl a))) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at hz
    linarith
  rcases Nat.lt_or_ge p 2 with hp | hp2
  · -- At most one positive square: the negated form has at least two.
    have hq2 : 2 ≤ q := by omega
    have hposw : ∀ b : Fin q, (fun i => -w i) (τ ((Equiv.sumComm (Fin q) (Fin p)) (Sum.inl b)))
        = 1 := by
      intro b; simp [hq1 b]
    have hnegw : ∀ a : Fin p, (fun i => -w i) (τ ((Equiv.sumComm (Fin q) (Fin p)) (Sum.inr a)))
        = -1 := by
      intro a; simp [hp1 a]
    have hQ' : ∀ z, -matrixQuadForm K z = ∑ i, (fun i => -w i) i * (f z i * f z i) := by
      intro z
      rw [hQ z]
      simp
    obtain ⟨e, he⟩ :=
      exists_signed_congruence_of_diagonal (n := n) (p := q) (q := p) (by omega)
        (Q := fun z => -matrixQuadForm K z) (fun i => -w i) f
        ((Equiv.sumComm (Fin q) (Fin p)).trans τ) hposw hnegw hQ'
    exact ⟨q, p, hq2, ⟨hpne⟩, by omega, e, Or.inr fun z => by
      have := he z; linarith⟩
  · obtain ⟨e, he⟩ :=
      exists_signed_congruence_of_diagonal hpq w f τ hp1 hq1 hQ
    exact ⟨p, q, hp2, ⟨hqne⟩, hpq, e, Or.inl he⟩

/-! ## Carrying a congruence across the free block

The equivalence produced above acts on the quadratic coordinates only.  Extended
by the identity on the free block it is still a continuous linear equivalence of
the ambient space, and `hasLocalVolumeOrder_comp_continuousLinearEquiv` transports
the pair back along it.
-/

/-- The congruence extended by the identity on the free block. -/
@[expose] public noncomputable def germCongruence (p q s : ℕ)
    (e : EuclideanSpace ℝ (Fin (p + q)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q))) :
    EuclideanSpace ℝ (Fin (p + q + s)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q + s)) :=
  (((splitLE (p + q) s).symm.trans
    (e.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin s))))).trans
      (splitLE (p + q) s)).toContinuousLinearEquiv

/-- On split coordinates the extension is `e` on the quadratic block and the
identity on the free block, which is the only property of it that is used. -/
public theorem germCongruence_splitLE (p q s : ℕ)
    (e : EuclideanSpace ℝ (Fin (p + q)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q)))
    (ξ : EuclideanSpace ℝ (Fin (p + q))) (ζ : EuclideanSpace ℝ (Fin s)) :
    germCongruence p q s e (splitLE (p + q) s (ξ, ζ)) = splitLE (p + q) s (e ξ, ζ) := by
  simp [germCongruence]

/-- **The band pair of `|Q(ξ) + g(ζ)|` for a form congruent to the model.**

This is `hasLocalVolumeOrder_freeBlockGerm` transported along the extension of
`e` by the identity.  The germ `g` is not touched by the transport — the
extension is the identity on the free block — so `g 0 = 0` is carried across
unchanged rather than re-derived. -/
public theorem hasLocalVolumeOrder_abs_add_germ_of_congruence {p q s : ℕ} [NeZero q]
    (hp : 2 ≤ p) {Q : EuclideanSpace ℝ (Fin (p + q)) → ℝ}
    (e : EuclideanSpace ℝ (Fin (p + q)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q)))
    (hQ : ∀ z, Q z = modelBandForm p q (e z))
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (hg : Continuous g) (hg0 : g 0 = 0) :
    HasLocalVolumeOrder
      (fun w : EuclideanSpace ℝ (Fin (p + q + s)) =>
        |Q ((euclideanProdEquiv (p + q) s).symm w).1
          + g (((euclideanProdEquiv (p + q) s).symm w).2)|)
      0 1 1 := by
  have hfun : (fun w : EuclideanSpace ℝ (Fin (p + q + s)) =>
      |Q ((euclideanProdEquiv (p + q) s).symm w).1
        + g (((euclideanProdEquiv (p + q) s).symm w).2)|)
      = freeBlockGerm p q s g ∘ (germCongruence p q s e) := by
    funext w
    obtain ⟨⟨ξ, ζ⟩, rfl⟩ := (splitLE (p + q) s).surjective w
    have hsym : (euclideanProdEquiv (p + q) s).symm (splitLE (p + q) s (ξ, ζ)) = (ξ, ζ) := by
      rw [coe_splitLE]
      exact (euclideanProdEquiv (p + q) s).symm_apply_apply (ξ, ζ)
    rw [Function.comp_apply, germCongruence_splitLE, hsym, coe_splitLE,
      freeBlockGerm_euclideanProdEquiv, hQ ξ]
  rw [hfun]
  refine hasLocalVolumeOrder_comp_continuousLinearEquiv (germCongruence p q s e) ?_
  rw [map_zero]
  exact hasLocalVolumeOrder_freeBlockGerm p q s hp g hg hg0

/-! ## Print's Lemma 2, in full generality -/

/-- **Lemma 2 in full generality**: a nondegenerate indefinite quadratic form in
`n ≥ 3` variables, plus a continuous germ vanishing at the origin on a free
block, has band pair `(1,1)`.

The form arrives as an explicit symmetric matrix with nonvanishing determinant
and one vector of each sign — the shape a Stage 3 caller can check — and the germ
is arbitrary beyond continuity and `g 0 = 0`.  Nothing else is assumed: no
frontier hypothesis appears here or in any lemma this uses.

The negative branch of `exists_model_congruence` is absorbed by running the
argument at `-g`, which is continuous and vanishes at the origin, and observing
`|(-Q) + (-g)| = |Q + g|`. -/
public theorem hasLocalVolumeOrder_abs_matrixQuadForm_add_germ {n s : ℕ} (h3 : 3 ≤ n)
    (K : Matrix (Fin n) (Fin n) ℝ) (hsymm : K.IsSymm) (hdet : K.det ≠ 0)
    (hpos : ∃ z, 0 < matrixQuadForm K z) (hneg : ∃ z, matrixQuadForm K z < 0)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (hg : Continuous g) (hg0 : g 0 = 0) :
    HasLocalVolumeOrder
      (fun w : EuclideanSpace ℝ (Fin (n + s)) =>
        |matrixQuadForm K ((euclideanProdEquiv n s).symm w).1
          + g (((euclideanProdEquiv n s).symm w).2)|)
      0 1 1 := by
  obtain ⟨p, q, hp2, hqz, hpq, e, hcong⟩ :=
    exists_model_congruence h3 K hsymm hdet hpos hneg
  subst hpq
  have : NeZero q := hqz
  rcases hcong with hc | hc
  · exact hasLocalVolumeOrder_abs_add_germ_of_congruence hp2 e hc g hg hg0
  · have hneg' : ∀ z, -matrixQuadForm K z = modelBandForm p q (e z) := by
      intro z; rw [hc z]; ring
    have hmain := hasLocalVolumeOrder_abs_add_germ_of_congruence (Q := fun z => -matrixQuadForm K z)
      hp2 e hneg' (fun ζ => -g ζ) hg.neg (by simp [hg0])
    have hfun : (fun w : EuclideanSpace ℝ (Fin (p + q + s)) =>
        |(fun z => -matrixQuadForm K z) ((euclideanProdEquiv (p + q) s).symm w).1
          + (fun ζ => -g ζ) (((euclideanProdEquiv (p + q) s).symm w).2)|)
        = fun w : EuclideanSpace ℝ (Fin (p + q + s)) =>
          |matrixQuadForm K ((euclideanProdEquiv (p + q) s).symm w).1
            + g (((euclideanProdEquiv (p + q) s).symm w).2)| := by
      funext w
      rw [← abs_neg]
      ring_nf
    rwa [hfun] at hmain

end AISafetyAtlas.SingularLearning
