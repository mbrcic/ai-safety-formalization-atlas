import SocialChoice.Impossibilities.GibbardSatterthwaite.Common

namespace SocialChoice

/-!
# Gibbard-Satterthwaite Induction Step: Case 1

Case 1 of the induction step: If the dictator in the cloned rule g is
voter i ∈ {3, ..., n} (i.e., i ≠ v₁), then i is also the dictator in f.

## Main Result

* `gs_case1`: If i ≠ v₁ is the dictator in g, then i.val is the dictator in f.
-/

open Finset

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [Nonempty A]

/-- Case 1: If dictator in g is voter i ∈ {3,...,n} (i.e., i.val ≠ v₁),
    then i.val is also a dictator in f. -/
theorem gs_case1
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (i : {w : V // w ≠ v₂}) (hi : i.val ≠ v₁)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' i}) :
    ∀ P : Profile V A, f P = {topChoice P i.val} := by
  intro P

  -- The key insight: we can derive f(P) = topChoice(P, i) from the fact that
  -- g dictates for i, combined with strategy-proofness.

  -- Define the reduced profile P' by restricting P to {w : V // w ≠ v₂}
  -- where v₂ is simply dropped.
  let P'_v1 : Profile {w : V // w ≠ v₂} A :=
    { pref := fun w => P.pref w.val }

  let P'_v2 : Profile {w : V // w ≠ v₂} A :=
    { pref := fun w => if w.val = v₁ then P.pref v₂ else P.pref w.val }

  -- From the cloned rule definition:
  -- g(P'_v1) = f(expanded profile where v₂ copies v₁)
  --          = f(P₁, P₁, P₃, ..., Pₙ) [using notation from the paper]

  -- By dictatorship of g at P'_v1: g(P'_v1) = {topChoice P'_v1 i}
  have hg_v1 : clonedRule f v₁ v₂ hne P'_v1 = {topChoice P'_v1 i} := hdict_g P'_v1

  -- By dictatorship of g at P'_v2: g(P'_v2) = {topChoice P'_v2 i}
  have hg_v2 : clonedRule f v₁ v₂ hne P'_v2 = {topChoice P'_v2 i} := hdict_g P'_v2

  -- Note that topChoice P'_v1 i = topChoice P i.val (since P'_v1.pref i = P.pref i.val)
  have htop_v1 : topChoice P'_v1 i = topChoice P i.val := by
    unfold topChoice
    congr 1

  -- And topChoice P'_v2 i = topChoice P i.val (since i.val ≠ v₁, so P'_v2.pref i = P.pref i.val)
  have htop_v2 : topChoice P'_v2 i = topChoice P i.val := by
    unfold topChoice
    congr 1
    simp only [P'_v2, hi, ite_false]

  -- Let a = topChoice P i.val (the dictator's choice)
  let a := topChoice P i.val

  -- So g(P'_v1) = {a} and g(P'_v2) = {a}
  rw [htop_v1] at hg_v1
  rw [htop_v2] at hg_v2

  -- Now unfold the cloned rule:
  -- clonedRule f v₁ v₂ hne P'_v1 = f(expandProfile v₁ v₂ hne P'_v1)
  -- The expanded profile of P'_v1 has:
  --   - v₁ → P.pref v₁
  --   - v₂ → P.pref v₁ (copies v₁)
  --   - w ≠ v₂ → P.pref w
  -- This is the profile (P₁, P₁, P₃, ..., Pₙ)

  -- Similarly for P'_v2, the expanded profile has:
  --   - v₁ → P.pref v₂ (since P'_v2.pref ⟨v₁, hne⟩ = P.pref v₂)
  --   - v₂ → P.pref v₂ (copies v₁'s ballot which is P.pref v₂)
  --   - w ≠ v₂ → P.pref w
  -- This is the profile (P₂, P₂, P₃, ..., Pₙ)

  -- Let Q₁₁ = expandProfile v₁ v₂ hne P'_v1 (profile with v₂ copying v₁)
  -- Let Q₂₂ = expandProfile v₁ v₂ hne P'_v2 (profile with v₂ copying v₂, i.e., both equal P.pref v₂)

  let Q₁₁ := expandProfile v₁ v₂ hne P'_v1
  let Q₂₂ := expandProfile v₁ v₂ hne P'_v2

  have hQ₁₁ : f Q₁₁ = {a} := hg_v1
  have hQ₂₂ : f Q₂₂ = {a} := hg_v2

  -- Now, the actual profile P differs from both Q₁₁ and Q₂₂ only in some ballots.
  -- We need to use strategy-proofness to show f P = {a}.

  -- Strategy:
  -- 1. Q₁₁ differs from P only at v₂ (where Q₁₁ has P.pref v₁, and P has P.pref v₂)
  -- 2. By strategy-proofness, starting from Q₁₁, if we change v₂'s ballot to P.pref v₂,
  --    the outcome should either stay at a or move to something v₂ doesn't prefer over a (in Q₁₁).

  -- Note: Q₁₁ differs from P at v₂:
  -- Q₁₁.pref v₂ = P.pref v₁
  -- P.pref v₂ = P.pref v₂
  -- For w ≠ v₂: Q₁₁.pref w = P.pref w

  -- Actually let's check: expandProfile v₁ v₂ hne P'_v1 at v:
  -- if v = v₂: P'_v1.pref ⟨v₁, hne⟩ = P.pref v₁
  -- if v ≠ v₂: P'_v1.pref ⟨v, _⟩ = P.pref v

  -- So Q₁₁.pref v = if v = v₂ then P.pref v₁ else P.pref v

  -- Let's denote the outcome of f P as b
  let b := theWinner f P hf
  have hfP : f P = {b} := (eq_singleton_iff_theWinner_eq f P hf b).mpr rfl

  -- We want to show b = a

  -- Claim: P = updateProfile Q₁₁ v₂ (P.pref v₂)
  have hP_from_Q₁₁ : P = updateProfile Q₁₁ v₂ (P.pref v₂) := by
    ext w
    by_cases hwv₂ : w = v₂
    · rw [hwv₂, updateProfile_pref_self]
    · rw [updateProfile_pref_of_ne _ _ _ hwv₂]
      have h2 : Q₁₁.pref w = P.pref w := expandProfile_pref_of_ne v₁ v₂ hne P'_v1 hwv₂
      rw [h2]

  -- By strategy-proofness of f applied at Q₁₁:
  -- f Q₁₁ = {a}, f P = {b}
  -- => ¬ Prefers Q₁₁ v₂ b a
  have hfP1 : f (updateProfile Q₁₁ v₂ (P.pref v₂)) = {b} := by
    simpa [hP_from_Q₁₁.symm] using hfP
  have hsp1 : ¬ Prefers Q₁₁ v₂ b a := hf_sp Q₁₁ v₂ (P.pref v₂) a b hQ₁₁ hfP1

  -- Note: Prefers Q₁₁ v₂ uses Q₁₁.pref v₂ = P.pref v₁
  -- So hsp1 says: ¬ (b <_{P.pref v₁} a), i.e., a ≤_{P.pref v₁} b

  -- Similarly, we have Q₂₂ differs from P at v₁:
  -- Q₂₂.pref v = if v = v₂ then P.pref v₂ else (if v = v₁ then P.pref v₂ else P.pref v)
  -- So Q₂₂.pref v₁ = P.pref v₂, Q₂₂.pref v₂ = P.pref v₂, Q₂₂.pref w = P.pref w for w ≠ v₁, v₂

  -- Claim: P = updateProfile Q₂₂ v₁ (P.pref v₁)
  have hP_from_Q₂₂ : P = updateProfile Q₂₂ v₁ (P.pref v₁) := by
    ext w
    by_cases hwv₁ : w = v₁
    · rw [hwv₁, updateProfile_pref_self]
    · have h1 : (updateProfile Q₂₂ v₁ (P.pref v₁)).pref w = Q₂₂.pref w :=
        updateProfile_pref_of_ne Q₂₂ v₁ (P.pref v₁) hwv₁
      by_cases hwv₂ : w = v₂
      · have h2 : Q₂₂.pref w = P.pref w := by
          have hb : Q₂₂.pref w = P'_v2.pref ⟨v₁, hne⟩ := by
            rw [hwv₂]; exact expandProfile_pref_v2 v₁ v₂ hne P'_v2
          rw [hb, hwv₂]; exact if_pos rfl
        rw [h1, h2]
      · have h2 : Q₂₂.pref w = P.pref w := by
          have hb : Q₂₂.pref w = P'_v2.pref ⟨w, hwv₂⟩ := expandProfile_pref_of_ne v₁ v₂ hne P'_v2 hwv₂
          rw [hb]; exact if_neg hwv₁
        rw [h1, h2]

  have hfP2 : f (updateProfile Q₂₂ v₁ (P.pref v₁)) = {b} := by
    simpa [hP_from_Q₂₂.symm] using hfP
  have hsp2 : ¬ Prefers Q₂₂ v₁ b a := hf_sp Q₂₂ v₁ (P.pref v₁) a b hQ₂₂ hfP2

  -- Note: Prefers Q₂₂ v₁ uses Q₂₂.pref v₁ = P.pref v₂
  -- So hsp2 says: ¬ (b <_{P.pref v₂} a), i.e., a ≤_{P.pref v₂} b

  -- Now we have:
  -- - a ≤_{P.pref v₁} b  (from hsp1)
  -- - a ≤_{P.pref v₂} b  (from hsp2)

  -- But we need to show a = b.

  -- The key insight is to use strategy-proofness in the other direction too.
  -- Consider changing v₂'s ballot in P to match v₁ (going backwards):

  -- f P = {b}, and if we change v₂'s ballot to P.pref v₁:
  have hQ₁₁_from_P : Q₁₁ = updateProfile P v₂ (P.pref v₁) := by
    ext v
    by_cases hv : v = v₂
    · rw [hv]
      have h1 : Q₁₁.pref v₂ = P.pref v₁ := expandProfile_pref_v2 v₁ v₂ hne P'_v1
      rw [h1, updateProfile_pref_self]
    · have h1 : Q₁₁.pref v = P.pref v := expandProfile_pref_of_ne v₁ v₂ hne P'_v1 hv
      have h2 : (updateProfile P v₂ (P.pref v₁)).pref v = P.pref v :=
        updateProfile_pref_of_ne P v₂ (P.pref v₁) hv
      rw [h1, h2]

  -- Actually we need P without the rewriting
  have hfP_orig : f P = {b} := hfP

  rw [hQ₁₁_from_P] at hQ₁₁
  have hsp3 : ¬ Prefers P v₂ a b := hf_sp P v₂ (P.pref v₁) b a hfP_orig hQ₁₁

  -- Similarly in the other direction for v₁:
  have hQ₂₂_from_P : Q₂₂ = updateProfile P v₁ (P.pref v₂) := by
    ext v
    by_cases hv₁ : v = v₁
    · rw [hv₁]
      have h1 : Q₂₂.pref v₁ = P.pref v₂ := by
        have hb : Q₂₂.pref v₁ = P'_v2.pref ⟨v₁, hne⟩ := expandProfile_pref_of_ne v₁ v₂ hne P'_v2 hne
        rw [hb]; exact if_pos rfl
      rw [h1, updateProfile_pref_self]
    · by_cases hv₂ : v = v₂
      · rw [hv₂]
        have h1 : Q₂₂.pref v₂ = P.pref v₂ := by
          have hb : Q₂₂.pref v₂ = P'_v2.pref ⟨v₁, hne⟩ := expandProfile_pref_v2 v₁ v₂ hne P'_v2
          rw [hb]; exact if_pos rfl
        have h2 : (updateProfile P v₁ (P.pref v₂)).pref v₂ = P.pref v₂ :=
          updateProfile_pref_of_ne P v₁ (P.pref v₂) (hv₂ ▸ hv₁)
        rw [h1, h2]
      · have h1 : Q₂₂.pref v = P.pref v := by
          have hb : Q₂₂.pref v = P'_v2.pref ⟨v, hv₂⟩ := expandProfile_pref_of_ne v₁ v₂ hne P'_v2 hv₂
          rw [hb]; exact if_neg hv₁
        have h2 : (updateProfile P v₁ (P.pref v₂)).pref v = P.pref v :=
          updateProfile_pref_of_ne P v₁ (P.pref v₂) hv₁
        rw [h1, h2]

  rw [hQ₂₂_from_P] at hQ₂₂
  have hsp4 : ¬ Prefers P v₁ a b := hf_sp P v₁ (P.pref v₂) b a hfP_orig hQ₂₂

  -- Now hsp3 says: ¬ (a <_{P.pref v₂} b), i.e., b ≤_{P.pref v₂} a
  -- Combined with hsp2: a ≤_{P.pref v₂} b
  -- This gives a = b under P.pref v₂

  -- Similarly for v₁'s preferences

  -- From hsp1: ¬ (b <_{P.pref v₁} a), so a ≤_{P.pref v₁} b
  -- From hsp4: ¬ (a <_{P.pref v₁} b), so b ≤_{P.pref v₁} a
  -- Together: a = b under P.pref v₁

  -- Use linear order antisymmetry to show b = a, then rewrite the outcome
  unfold Prefers at hsp1 hsp4
  have hQ₁₁_v₂ : Q₁₁.pref v₂ = P.pref v₁ := by
    simp [Q₁₁, expandProfile, P'_v1]

  have hsp1' : ¬ (P.pref v₁).lt b a := by
    rw [hQ₁₁_v₂] at hsp1
    exact hsp1

  have hsp4' : ¬ (P.pref v₁).lt a b := by
    simpa using hsp4

  letI := P.pref v₁
  have hle1 : a ≤ b := not_lt.mp hsp1'
  have hle2 : b ≤ a := not_lt.mp hsp4'
  have hba : a = b := le_antisymm hle1 hle2

  have hba' : b = a := hba.symm
  -- Conclude
  simpa [hba'] using hfP_orig

end SocialChoice
