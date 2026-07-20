import SocialChoice.Profile

/-!
# Ballot-level shim for the Gibbard–Satterthwaite port

Root cause of the 4.27 -> 4.31 breakage: a ballot is a bundled `LinearOrder A`
(`Profile.pref : V -> LinearOrder A`).  Proofs discharge preference goals with
`simp [Prefers, ...]`, which unfolds `Prefers P v a b = (P.pref v).lt a b` down
the `LinearOrder -> PartialOrder -> Preorder -> LT` instance chain.  Between
Mathlib versions that chain's *syntactic* spelling changes, so two defeq terms
stop unifying ("Type mismatch after simplification" / "simp made no progress").

Fix: reason at the **ballot** level and keep `Prefers` sealed.  `Prefers P v a b`
depends on `P.pref v` only, so ballot equality transports it without ever
touching the `.lt` instance path.  These lemmas are version-stable: they mention
only function equality of ballots, never `LinearOrder`'s internal fields.
-/

namespace SocialChoice

variable {V W A : Type} [Fintype V] [Fintype W] [Fintype A]

/-- The workhorse: transport `Prefers` across ballot equality without unfolding
`.lt`.  Replaces every `simpa [Prefers, <constructor>] using h`. -/
theorem prefers_congr_ballot (P : Profile V A) (Q : Profile W A)
    (v : V) (w : W) (h : P.pref v = Q.pref w) (a b : A) :
    Prefers P v a b ↔ Prefers Q w a b := by
  unfold Prefers; rw [h]

/-- `TopRank` transported across ballot equality. -/
theorem topRank_congr_ballot (P : Profile V A) (Q : Profile W A)
    (v : V) (w : W) (h : P.pref v = Q.pref w) (c : A) :
    TopRank P v c ↔ TopRank Q w c := by
  unfold TopRank
  constructor <;> intro htop d hd <;>
    [exact (prefers_congr_ballot P Q v w h c d).mp (htop d hd);
     exact (prefers_congr_ballot P Q v w h c d).mpr (htop d hd)]

/-- `BottomRank` transported across ballot equality. -/
theorem bottomRank_congr_ballot (P : Profile V A) (Q : Profile W A)
    (v : V) (w : W) (h : P.pref v = Q.pref w) (c : A) :
    BottomRank P v c ↔ BottomRank Q w c := by
  unfold BottomRank
  constructor <;> intro hbot d hd <;>
    [exact (prefers_congr_ballot P Q v w h d c).mp (hbot d hd);
     exact (prefers_congr_ballot P Q v w h d c).mpr (hbot d hd)]

/-! ## Ballot projections for the `Profile` constructors

Each rewrites `(constructor ...).pref v` to the selected ballot at the *data*
level (no `.lt`).  Feed the resulting equality into `prefers_congr_ballot`. -/

@[simp] theorem constantProfile_pref (r : LinearOrder A) (v : V) :
    (constantProfile (V := V) r).pref v = r := rfl

@[simp] theorem addVoter_pref_old (P : Profile V A) (ballot : LinearOrder A)
    (v : V) : (addVoter P ballot).pref (Sum.inl v) = P.pref v := rfl

@[simp] theorem addVoter_pref_new (P : Profile V A) (ballot : LinearOrder A)
    (u : Unit) : (addVoter P ballot).pref (Sum.inr u) = ballot := rfl

@[simp] theorem unionProfiles_pref_left (P₁ : Profile V A) (P₂ : Profile W A)
    (v : V) : (unionProfiles P₁ P₂).pref (Sum.inl v) = P₁.pref v := rfl

@[simp] theorem unionProfiles_pref_right (P₁ : Profile V A) (P₂ : Profile W A)
    (w : W) : (unionProfiles P₁ P₂).pref (Sum.inr w) = P₂.pref w := rfl

@[simp] theorem permuteVoters_pref (P : Profile V A) (σ : Equiv.Perm V) (v : V) :
    (permuteVoters P σ).pref v = P.pref (σ v) := rfl

end SocialChoice
