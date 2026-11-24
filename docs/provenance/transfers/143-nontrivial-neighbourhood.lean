import AISafetyAtlas.Combinatorics.PermInvariance

/-!
Igel & Toussaint (2004), Theorem 4, p. 318. "A non-trivial neighborhood relation
on `𝒳` is not invariant under permutations of `𝒳`, i.e.,
`∃ xᵢ, xⱼ ∈ 𝒳, π ∈ Π(𝒳) : n(xᵢ, xⱼ) ≠ n(π(xᵢ), π(xⱼ))`." A neighborhood relation
is a symmetric `n : 𝒳 × 𝒳 → {0, 1}`; non-trivial means some distinct pair has
`n = 1` and some distinct pair has `n = 0`; `𝒳` is a finite search space (§2).
The cited declaration is `AISafetyAtlas.Combinatorics.exists_perm_rel_not_iff`
(any type `X`, any `Prop`-valued relation `r`, symmetric or not).

The map sends a Lean instance `(X, r)` with witnesses `(a, b)` (distinct,
related) and `(c, d)` (distinct, unrelated) to a neighbourhood on the three
points `Fin 3`. Each unordered edge is decoded to an ordered pair of `X`: the
edge `{0, 2}` to `(c, d)`, the edges `{0, 1}` and `{1, 2}` to `(a, b)`. The
value on an edge is the truth value of `r` at its decoded pair, the value on
the diagonal is `0`. This is symmetric and non-trivial. A printed mismatch at
`(p, q, σ)` lies off the diagonal (a permutation keeps the diagonal), so it
gives two decoded off-diagonal pairs of `X` on which `r` differs; the
permutation of `X` carrying one onto the other (`exists_perm_apply_eq_of_ne`,
a two-swap lemma) is the Lean witness.

The decoding only reads `r` at the two witness pairs, so the image is always
the path `0 - 1 - 2`; the transfer needs print's conclusion only to name which
two decoded pairs differ.

Checked: `lake env lean docs/provenance/transfers/143-nontrivial-neighbourhood.lean`
-/

namespace Transfer143

open AISafetyAtlas.Combinatorics

universe u

/-- Print's Theorem 4 on every finite search space. -/
def PrintStatement : Prop :=
  ∀ (X : Type u) [Fintype X] (n : X → X → Fin 2), (∀ x y, n x y = n y x) →
    (∃ xi xj, xi ≠ xj ∧ n xi xj = 1) → (∃ xk xl, xk ≠ xl ∧ n xk xl = 0) →
    ∃ (xi xj : X) (π : Equiv.Perm X), n xi xj ≠ n (π xi) (π xj)

/-- The cited statement. -/
def LeanStatement : Prop :=
  ∀ (X : Type u) (r : X → X → Prop), (∃ a b : X, a ≠ b ∧ r a b) →
    (∃ a b : X, a ≠ b ∧ ¬ r a b) → ∃ (a b : X) (π : Equiv.Perm X), ¬ (r (π a) (π b) ↔ r a b)

/-- The edge decoding: `{0, 2}` to `e₂`, every other pair to `e₁`. -/
def dec {X : Type u} (e₁ e₂ : X × X) (p q : Fin 3) : X × X :=
  if (p = 0 ∧ q = 2) ∨ (p = 2 ∧ q = 0) then e₂ else e₁

open Classical in
/-- The image neighbourhood: `r` at the decoded pair off the diagonal, `0` on it. -/
noncomputable def phi {X : Type u} (r : X → X → Prop) (e₁ e₂ : X × X) :
    Fin 3 → Fin 3 → Fin 2 :=
  fun p q => if p = q then 0 else if r (dec e₁ e₂ p q).1 (dec e₁ e₂ p q).2 then 1 else 0

theorem H {X : Type u} (r : X → X → Prop) {a b c d : X} (hab : r a b) (hcd : ¬ r c d) :
    (∀ p q, phi r (a, b) (c, d) p q = phi r (a, b) (c, d) q p) ∧
      (∃ p q, p ≠ q ∧ phi r (a, b) (c, d) p q = 1) ∧
      (∃ p q, p ≠ q ∧ phi r (a, b) (c, d) p q = 0) := by
  refine ⟨fun p q => ?_, ⟨0, 1, by decide, ?_⟩, ⟨0, 2, by decide, ?_⟩⟩
  · have hd : dec (a, b) (c, d) p q = dec (a, b) (c, d) q p := by
      unfold dec
      split_ifs <;> first | rfl | (exfalso; tauto)
    by_cases hpq : p = q
    · subst hpq; rfl
    · simp only [phi, hpq, Ne.symm hpq, if_false]
      rw [hd]
  · simp [phi, dec, hab]
  · simp [phi, dec, hcd]

theorem C {X : Type u} (r : X → X → Prop) {a b c d : X} (hab : a ≠ b) (hcd : c ≠ d)
    (hP : ∃ (p q : Fin 3) (σ : Equiv.Perm (Fin 3)),
      phi r (a, b) (c, d) p q ≠ phi r (a, b) (c, d) (σ p) (σ q)) :
    ∃ (x y : X) (π : Equiv.Perm X), ¬ (r (π x) (π y) ↔ r x y) := by
  obtain ⟨p, q, σ, hne⟩ := hP
  have hoff : ∀ p q : Fin 3, (dec (a, b) (c, d) p q).1 ≠ (dec (a, b) (c, d) p q).2 := by
    intro p q
    unfold dec
    split_ifs
    · exact hcd
    · exact hab
  have hpq : p ≠ q := by
    rintro rfl
    exact hne (by simp [phi])
  have hσ : σ p ≠ σ q := fun h => hpq (σ.injective h)
  set u := dec (a, b) (c, d) p q
  set v := dec (a, b) (c, d) (σ p) (σ q)
  have hr : ¬ (r u.1 u.2 ↔ r v.1 v.2) := by
    intro hiff
    apply hne
    simp only [phi, hpq, hσ, if_false]
    split_ifs <;> first | rfl | (exfalso; tauto)
  obtain ⟨π, h1, h2⟩ := exists_perm_apply_eq_of_ne (hoff (σ p) (σ q)) (hoff p q)
  refine ⟨v.1, v.2, π, ?_⟩
  rw [h1, h2]
  exact hr

theorem lean_of_print : PrintStatement.{0} → LeanStatement.{u} := by
  intro hP X r ⟨a, b, hab, hr⟩ ⟨c, d, hcd, hnr⟩
  obtain ⟨hsymm, hedge, hnon⟩ := H r hr hnr
  exact C r hab hcd (hP (Fin 3) (phi r (a, b) (c, d)) hsymm hedge hnon)

theorem print_of_lean : LeanStatement.{u} → PrintStatement.{u} := by
  intro hL X _ n _ ⟨xi, xj, hij, h1⟩ ⟨xk, xl, hkl, h0⟩
  obtain ⟨x, y, π, h⟩ := hL X (fun x y => n x y = 1) ⟨xi, xj, hij, h1⟩
    ⟨xk, xl, hkl, by rw [h0]; decide⟩
  exact ⟨x, y, π, fun he => h (by rw [he])⟩

end Transfer143
