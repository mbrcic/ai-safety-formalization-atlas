module

public import Mathlib.Data.Fintype.EquivFin

/-!
# Vendored Arrow proof

This is CC Liang's Lean 4 proof of Arrow's impossibility theorem from
https://github.com/ChihChengLiang/arrow at commit
`758398779decc66d2830a70b02597b0f22030181`, licensed Apache-2.0.
The original `Arrow/Arrow.lean` SHA-256 is
`ed006bc3ddc4249dfbff213e2f9f32b59a71721827060a25a46f8e5980ab7ab0`.

The proof body is unchanged. The atlas adds the modern `module` marker, public
declaration visibility, and this namespace. It converts the upstream `Profile`
and `SWF` definitions to reducible abbreviations so the adapted interfaces
elaborate across Lean 4.32's public-module boundary. It also adds four
`Iff.rfl` elimination lemmas required across that boundary:
`Preorder'.lt_iff`, `unanimity_iff`, `iia_iff`, and
`nonDictatorship_iff`. These lemmas expose existing definitions; they do not
change the Arrow proof.
-/

namespace AISafetyAtlas.Upstream.Arrow

noncomputable section
open Classical

/-! ## Preorder'

A total preorder over candidates `α`, representing an individual's preference ranking.
-/
variable {α : Type}

-- ANCHOR: Preorder
/-- A total preorder: reflexive, transitive, and total. -/
public structure Preorder' (α : Type) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ a b c, le a b → le b c → le a c
  total : ∀ a b, le a b ∨ le b a
-- ANCHOR_END: Preorder

-- ANCHOR: StrictPref
/-- Strict preference: `a` is strictly preferred to `b` iff `a ≤ b` but not `b ≤ a`. -/
@[simp]
public def Preorder'.lt (p : Preorder' α) (a b : α) : Prop :=
  p.le a b ∧ ¬p.le b a
-- ANCHOR_END: StrictPref

/-- Public elimination rule for strict preference. Atlas addition. -/
public theorem Preorder'.lt_iff (p : Preorder' α) (a b : α) :
    p.lt a b ↔ p.le a b ∧ ¬p.le b a :=
  Iff.rfl

-- ANCHOR: Notation
-- Notation: `a ≻[p] b` means voter with preference `p` strictly prefers `a` over `b`
notation a " ≻[" p  "] " b => Preorder'.lt p b a
notation a " ≽[" p  "] " b => Preorder'.le p b a
notation a " ≻[" p  "] " b "≻ " c => (a ≻[p] b) ∧ b ≻[p] c
notation a " ≽[" p  "] " b "≻ " c => (a ≽[p] b) ∧ b ≻[p] c
-- ANCHOR_END: Notation

public lemma Preorder'.lt_asymm {p : Preorder' α} {a b : α} :
    p.lt a b → ¬ p.lt b a := by intro ⟨_, hnba⟩ ⟨hba, _⟩; exact hnba hba

public lemma Preorder'.not_lt {α : Type} {p : Preorder' α} {a b : α} :
    ¬ p.lt a b ↔ p.le b a := by simp [Preorder'.lt, p.total]

public lemma Preorder'.lt_trans {p : Preorder' α} {a b c : α}
    (h1 : p.lt a b) (h2 : p.lt b c) : p.lt a c := by
    constructor
    . exact p.trans _ _ _ h1.1 h2.1
    . intro h; exact h1.2 (p.trans _ _ _ h2.1 h)

public lemma Preorder'.lt_of_lt_of_le {p : Preorder' α} {a b c : α}
    (hab : p.lt a b) (hbc : p.le b c) : p.lt a c := by
    simp [Preorder'.lt] at hab ⊢; constructor
    . exact p.trans _ _ _ hab.1 hbc
    . intro h; exact absurd (p.trans _ _ _ hbc h) hab.2

/-- The three possible outcomes when comparing two elements under a total preorder. -/
public inductive Cmp (p : Preorder' α) (a b : α) : Type
  | Indiff (h₁ : p.le a b) (h₂ : p.le b a) : Cmp p a b
  | LT     (h  : p.le a b) (hn : ¬p.le b a) : Cmp p a b
  | GT     (hn : ¬p.le a b) (h  : p.le b a)  : Cmp p a b

public noncomputable def Preorder'.cmp (p : Preorder' α) (a b : α) : Cmp p a b :=
  if hab : p.le a b then
    if hba : p.le b a then Cmp.Indiff hab hba
    else Cmp.LT hab hba
  else Cmp.GT hab (p.total a b |>.resolve_left hab)


/-! ## Social Welfare Function

Core definitions for Arrow's theorem: profiles, SWFs, and the three key properties.
-/
variable {N : ℕ}

-- ANCHOR: Profile
/-- A preference profile assigns each voter `i ∈ Fin N` their preference ordering. -/
public abbrev Profile (α : Type) (N : ℕ) := Fin N → Preorder' α
-- ANCHOR_END: Profile

-- ANCHOR: SWF
/-- A Social Welfare Function aggregates individual preferences into a social ordering. -/
public abbrev SWF (α : Type) (N : ℕ) := Profile α N → Preorder' α
-- ANCHOR_END: SWF

-- ANCHOR: Dictates
/-- Voter `k` is a dictator for the pair `(a, b)` if whenever `k` prefers `a` over `b`,
    society also prefers `a` over `b`. -/
public def Dictates (R : SWF α N) (k : Fin N) (a b : α): Prop :=
  ∀ (p: Profile α N ), (a ≻[p k] b) → a ≻[R p] b
-- ANCHOR_END: Dictates

-- ANCHOR: AgreeOn
/-- Two profiles agree on `(a, b)` if every voter ranks `a` vs `b` the same way in both. -/
@[simp]
public def AgreeOn (p q : Profile α N) (a b : α) : Prop :=
  ∀ i, ((a ≽[p i] b) ↔ a ≽[q i] b) ∧ ((b ≽[p i] a) ↔ b ≽[q i] a)
-- ANCHOR_END: AgreeOn

-- ANCHOR: Unanimity
/-- **Unanimity** (Pareto): If all voters prefer `a` over `b`, so does society. -/
public def Unanimity (R : SWF α N) : Prop :=
  ∀ (p: Profile α N) (a b: α), (∀ i: Fin N, a ≻[p i] b) → a ≻[R p] b
-- ANCHOR_END: Unanimity

-- ANCHOR: IIA
/-- **Independence of Irrelevant Alternatives**: The social ranking of `a` vs `b`
    depends only on individual rankings of `a` vs `b`. -/
public def IIA (R : SWF α N) : Prop :=
  ∀ (p q: Profile α N) (a b: α),
    AgreeOn p q a b → ((a ≽[R p] b) ↔ a ≽[R q] b) ∧ ((b ≽[R p] a) ↔ b ≽[R q] a)
-- ANCHOR_END: IIA

-- ANCHOR: NonDictatorship
/-- **Non-Dictatorship**: No single voter dictates the outcome for all pairs. -/
public def NonDictatorship (R : SWF α N): Prop :=
  ¬ (∃ i: Fin N, ∀ (a b: α), (a ≠ b) → Dictates R i a b)
-- ANCHOR_END: NonDictatorship

/-! ## Preference Construction

We construct concrete preference orderings to build test profiles for the proof.
Given three alternatives, `prefer a₀ a₁ a₂ tie` ranks them with optional ties.
-/

-- ANCHOR: Tie
/-- Where ties occur in a 3-element preference ranking -/
public inductive Tie | Not | Top | Bot
-- ANCHOR_END: Tie

@[simp]
public def prefer_ifs (x y a₀ _a₁ a₂ : α) (tie : Tie): Prop :=
  match tie with
  | .Not =>
    if x = a₂ then True              -- a₂ is bottom
    else if y = a₀ then True         -- a₀ is top
    else if x = a₀ then y = a₀       -- only a₀ ≤ a₀
    else if y = a₂ then x = a₂       -- only a₂ ≥ a₂
    else True
  | .Top =>
    if y = a₂ then x = a₂           -- only a₂ ≥ a₂ (a₂ is bottom)
    else if x = a₂ then True        -- a₂ ≤ everything else
    else True                        -- a₀ ~ a₁: both directions
  | .Bot =>
    if x = a₀ then y = a₀           -- only a₀ ≤ a₀ (a₀ is top)
    else if y = a₀ then True        -- everything else ≤ a₀
    else True                        -- a₁ ~ a₂: both directions

-- ANCHOR: prefer
/-- Construct a preference ordering with optional ties:
    - `Tie.Not`: a₀ > a₁ > a₂ (strict ranking)
    - `Tie.Top`: a₀ ~ a₁ > a₂ (top two tied)
    - `Tie.Bot`: a₀ > a₁ ~ a₂ (bottom two tied) -/
public def prefer (a₀ _a₁ a₂ : α) (tie : Tie) (h02 : a₀ ≠ a₂) : Preorder' α where
-- ANCHOR_END: prefer
  le x y := prefer_ifs x y a₀ _a₁ a₂ tie
  refl _ := by cases tie <;> simp
  trans _ _ _ _ _ := by unfold prefer_ifs at *; split <;> split_ifs <;> simp_all
  total a b := by unfold prefer_ifs at *; split <;> by_cases a = a₂ <;> by_cases b = a₀ <;> simp_all

/-! ## Pivotal Voter

The key construction: we find the "pivotal voter" who flips society's preference.
Starting from a profile where everyone prefers `b ≻ a`, we flip voters one by one
to prefer `a ≻ b`. By unanimity, society eventually flips too. The first voter
whose flip changes society's preference is the pivotal voter.
-/
variable [NeZero N] {R : SWF α N}

-- ANCHOR: canonicalSwap
/-- A family of profiles indexed by `k ∈ Fin (N+1)`:
    voters `0..k-1` prefer `b ≻ a`, voters `k..N-1` prefer `a ≻ b`. -/
@[simp]
public def canonicalSwap (a b : α) (hab : a ≠ b) : Fin (N+1) → Profile α N :=
  fun k: Fin (N+1) =>
    fun i: Fin N => if i < k.val
      -- `prefer` takes 3 items, we duplicate middle as a workaround
      then prefer b b a .Not hab.symm  -- b on top
      else prefer a b b .Not hab            -- a on top
-- ANCHOR_END: canonicalSwap

-- ANCHOR: flipping
/-- `flipping R a b hab k` holds iff society prefers `b ≻ a` when voters `0..k` prefer `b ≻ a`. -/
public def flipping (R : SWF α N) (a b : α) (hab : a ≠ b) :=
  fun k: Fin N => ¬ a ≻[R (canonicalSwap a b hab k.succ)] b
-- ANCHOR_END: flipping

/-- By unanimity, a flip must occur: when all voters prefer `b ≻ a`, so does society. -/
public lemma flip_exists (R : SWF α N) (a b : α) (hab : a ≠ b) (hu : Unanimity R):
    ∃ k, flipping R a b hab k := by
  use (0:Fin N).rev
  unfold flipping canonicalSwap
  simp [Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne N))]
  intros
  exact (show b ≻[R (fun _ => prefer b b a .Not hab.symm)] a from
          hu _ _ _ (fun _ => by simp [prefer, hab, hab.symm])).1

-- ANCHOR: pivoter
/-- The pivotal voter for `(a, b)`: the minimum `k` where society flips from `a ≻ b` to `b ≻ a`. -/
public noncomputable def pivoter (a b : α) (hab : a ≠ b) (hu : Unanimity R) : Fin N :=
  Fin.find (flipping R a b hab) (flip_exists R a b hab hu)
-- ANCHOR_END: pivoter

-- ANCHOR: no_flip
/-- Before the pivotal voter, society still prefers `a ≻ b`. -/
public lemma no_flip (a b : α) {hab : a ≠ b} {i n_ab : Fin N} {hu: Unanimity R}
  (hnab : pivoter a b hab hu = n_ab) (hilt: i < n_ab)
  : a ≻[R (canonicalSwap a b hab i.succ)] b := by
-- ANCHOR_END: no_flip
  subst n_ab
  have h := Fin.find_min (flip_exists R a b hab hu) hilt
  unfold flipping at h; push Not at h; exact h

-- ANCHOR: flipped
/-- At the pivotal voter, society flips to `b ≻ a`. -/
public lemma flipped (a b : α)
  {n_ab: Fin N} {hab : a ≠ b} {hu: Unanimity R}
  (hnab : pivoter a b hab hu = n_ab):
    b ≽[R (canonicalSwap a b hab n_ab.succ)] a := by
-- ANCHOR_END: flipped
  apply Preorder'.not_lt.mp
  show ¬a ≻[R (canonicalSwap a b hab n_ab.succ)] b
  rw[← hnab]
  exact Fin.find_spec (flip_exists R a b hab hu)

-- ANCHOR: nab_dictate_bc
/-- The pivotal voter for `(a, b)` dictates the pair `(b, c)`. -/
public lemma nab_dictate_bc (a b c: α) {n_ab : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hIIA: IIA R)
    (hnab : pivoter a b hab hu = n_ab)
    : Dictates R n_ab b c := by
-- ANCHOR_END: nab_dictate_bc
  have hba := hab.symm; have hca := hac.symm; have hcb := hbc.symm

  -- Magic profile 1
  -- 0    ... n_ab-1  prefer b ≻ c ≻ a
  -- n_ab ... N-1     prefer a ≻ b ≻ c
  -- Result: Society prefers a ≻ b ≻ c
  let mg1: Profile α N := fun i: Fin N =>
    if i < n_ab.val
      then prefer b c a .Not hba
      else prefer a b c .Not hac

  have habc: a ≻[R mg1] b ≻ c  := by
    constructor
    -- a ≻ b by definition of n_ab
    -- note that voter is `Fin N` but the family of profiles is `Fin N+1`.
    -- The profile zero is not handled in `flipping` related functions.
    . by_cases hn : n_ab = 0
      . -- Case n_ab = 0: All voters prefer a > b, use unanimity
        exact hu _ _ _ (fun i => show a ≻[mg1 i] b by simp [mg1, hn, prefer, hac, hba])
      . -- Case n_ab ≠ 0: Use no_flip
        let k := n_ab - 1
        have hk_succ : k.val + 1 = n_ab.val := by
          simp only [k, Fin.val_sub_one_of_ne_zero hn]
          exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hn))
        have hk : k.val < n_ab := by omega
        have hp : AgreeOn mg1 (canonicalSwap a b hab k.succ) a b := by
          intro i; unfold mg1; split_ifs with hi <;> simp [hk_succ, hi, prefer, hac, hab]
        simp [hIIA _ _ _ _ hp]
        exact no_flip a b hnab hk
    -- b ≻ c by unanimity
    . exact hu _ _ _ (fun i => show b ≻[mg1 i] c by
        unfold mg1; split_ifs <;> simp [prefer, hbc, hba, hcb, hca])

  -- `pp` has arbitrary preference on (b,c), except n_ab
  intro pp h_pp_bc

  -- Magic profile 2: match `pp` on (b,c)
  -- For i < n_ab: (b ? c) ≻ a (matching pp)
  -- For i = n_ab: b ≻ a ≻ c
  -- For i > n_ab: a ≻ (b ? c) (matching pp)
  -- Result: Society prefers b ≽ a ≻ c
  let mg2 : Profile α N := fun i: Fin N =>
    if i < n_ab
      then match (pp i).cmp b c with
        | .LT     _ _ => prefer c b a .Not hca
        | .GT     _ _ => prefer b c a .Not hba
        | .Indiff _ _ => prefer b c a .Top hba  -- b ~ c ≻ a
      else
        if i = n_ab then prefer b a c .Not hbc
        else match (pp i).cmp b c with
        | .LT     _ _ => prefer a c b .Not hab
        | .GT     _ _ => prefer a b c .Not hac
        | .Indiff _ _ => prefer a b c .Bot hac  -- a ≻ b ~ c

  have h_agree: AgreeOn pp mg2 b c := by
    simp [mg2, prefer]; intro i; split_ifs
    . -- i < n_ab
      split <;> simp_all
    . -- i = n_ab
      subst i n_ab; simp [h_pp_bc.1, h_pp_bc.2, hbc, hcb]
    . -- i > n_ab
      split <;> simp_all

  have hbac: b ≽[R mg2] a ≻ c := by
    constructor
    -- By IIA on nab pivoting defintion
    . have h_agree_ba: AgreeOn mg2 (canonicalSwap a b hab n_ab.succ) b a := by
        simp [mg2, prefer]; intro i;
        by_cases hi: i < n_ab
        . have :i.val < n_ab +1 := by omega
          simp [hi, this]; split <;> simp[hab, hba, hac]
        . by_cases hi2: i = n_ab
          . simp [hi2, hbc, hba]
          . have :¬ (i.val < n_ab +1 ):= by omega
            simp [hi, hi2, this]; split <;> simp [hac, hab]
      simp only [hIIA _ _ _ _ h_agree_ba]
      exact flipped a b hnab
    -- By IIA
    . have h_agree_ac: AgreeOn mg2 mg1 a c := by
        simp [mg2, mg1, prefer]; intro _; split_ifs <;> try split
        all_goals simp [hca, hac, hab, hcb]
      simp [hIIA _ _ _ _ h_agree_ac]
      exact (R mg1).lt_trans habc.2 habc.1

  simp [hIIA _ _ _ _ h_agree]
  -- transitivity from b ≽ a ≻ c
  show b ≻[R mg2] c
  exact (R mg2).lt_of_lt_of_le hbac.2 hbac.1

-- ANCHOR: nab_le_nbc
/-- The pivotal voter for `(a, b)` comes no later than the one for `(b, c)`. -/
public lemma nab_le_nbc (a b c: α) {n_ab n_bc : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hIIA: IIA R)
    (hnab : pivoter a b hab hu = n_ab)
    (hnbc : pivoter b c hbc hu = n_bc)
    : n_ab ≤ n_bc := by
-- ANCHOR_END: nab_le_nbc
  by_contra
  let cs := canonicalSwap b c hbc n_bc.succ
  exact absurd
    (show b ≻[R cs] c from nab_dictate_bc a b c hab hac hbc hu hIIA hnab cs
      (show b ≻[cs n_ab] c by simp [cs, prefer]; split_ifs <;> simp [hbc.symm, hbc]; omega))
    (show ¬ b ≻[R cs] c from flipped b c hnbc |> Preorder'.not_lt.mpr)

-- ANCHOR: ncb_le_nab
/-- The pivotal voter for `(c, b)` comes no later than the one for `(a, b)`. -/
public lemma ncb_le_nab (a b c: α) {n_ab n_cb : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hIIA: IIA R)
    (hnab : pivoter a b hab hu = n_ab)
    (hncb : pivoter c b hbc.symm hu = n_cb)
    : n_cb ≤ n_ab := by
-- ANCHOR_END: ncb_le_nab
  by_contra h; push Not at h
  let cs := canonicalSwap c b hbc.symm n_ab.succ
  exact absurd
    (show b ≻[R cs] c from nab_dictate_bc a b c hab hac hbc hu hIIA hnab cs
      (show b ≻[cs n_ab] c by simp [cs, prefer, hbc, hbc.symm]))
    (show ¬ b ≻[R cs] c from no_flip c b hncb h |> Preorder'.lt_asymm)

/-- Combining the above: `pivoter (c, b) ≤ pivoter (b, c)`. -/
public lemma ncb_le_nbc (a b c: α) {n_cb n_bc  : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hIIA: IIA R)
    (hncb : pivoter c b hbc.symm hu = n_cb)
    (hnbc : pivoter b c hbc hu = n_bc)
    : n_cb ≤ n_bc :=
  le_trans (ncb_le_nab a b c hab hac hbc hu hIIA rfl hncb) (nab_le_nbc a b c hab hac hbc hu hIIA rfl hnbc)

/-- All pivotal voters for pairs in `{a, b, c}` are the same:
    `pivoter (b, c) = pivoter (c, b) = pivoter (a, b)`. -/
public lemma nab_eq_nbc_ncb (a b c: α) {n_bc n_cb n_ab : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hIIA: IIA R)
    (hnbc : pivoter b c hbc hu = n_bc)
    (hncb : pivoter c b hbc.symm hu = n_cb)
    (hnab : pivoter a b hab hu = n_ab)
    : n_bc = n_cb ∧ n_cb = n_ab := by
  have h_nab_le_nbc := nab_le_nbc a b c hab hac hbc hu hIIA hnab hnbc
  have h_ncb_le_nab := ncb_le_nab a b c hab hac hbc hu hIIA hnab hncb
  have h_ncb_le_nbc := ncb_le_nbc a b c hab hac hbc hu hIIA hncb hnbc

  -- As b and c are distinct and arbitrary, n_bc ≤ n_cb also holds
  have h_nbc_le_ncb := ncb_le_nbc a c b hac hab hbc.symm hu hIIA hnbc hncb

  -- n_bc = n_cb = n_ab
  have h_nbc_eq_ncb := le_antisymm h_nbc_le_ncb h_ncb_le_nbc
  have h_nab_le_ncb := le_trans h_nab_le_nbc h_nbc_le_ncb
  have h_ncb_eq_nab := le_antisymm h_ncb_le_nab h_nab_le_ncb

  exact ⟨ h_nbc_eq_ncb, h_ncb_eq_nab⟩

-- ANCHOR: nab_dictate_xy
/-- The pivotal voter for any pair `(a, b)` dictates *every* pair `(x, y)`. -/
public lemma nab_dictate_xy (a b c x y: α) {n_ab : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxy : x ≠ y)
    (hu: Unanimity R) (hIIA: IIA R)
    (hnab : pivoter a b hab hu = n_ab)
    : Dictates R n_ab x y := by
-- ANCHOR_END: nab_dictate_xy
  -- prepare bridging equalities: n_ab = n_bc = n_cb
  have := nab_eq_nbc_ncb a b c hab hac hbc hu hIIA rfl rfl rfl
  by_cases hxb: x ≠ b <;> by_cases hxc: x ≠ c <;> by_cases hyc: y ≠ c <;> simp_all <;> try subst x y
  -- x ∉ {b, c}, y ≠ c, bridging from n_cx = n_bc = n_ab
  . have := nab_dictate_bc c x y (Ne.symm hxc) (Ne.symm hyc) hxy hu hIIA rfl
    have := nab_eq_nbc_ncb b c x hbc (Ne.symm hxb) (Ne.symm hxc) hu hIIA rfl rfl rfl
    simp_all
  -- x ∉ {b, c}, y = c, bridging from n_bx = n_cb = n_ab
  . have := nab_dictate_bc b x c (Ne.symm hxb) hbc hxc hu hIIA rfl
    have := nab_eq_nbc_ncb c b x (Ne.symm hbc) (Ne.symm hxc) (Ne.symm hxb) hu hIIA rfl rfl rfl
    simp_all
  -- x = c, y ≠ c
  . by_cases hyb: y ≠ b
    -- n_bc = n_ab
    . have := nab_dictate_bc b c y hbc (Ne.symm hyb) (Ne.symm hyc) hu hIIA rfl
      simp_all
    -- n_ac = n_cb = n_ab
    . have := nab_dictate_bc a c b hac hab (Ne.symm hbc) hu hIIA rfl
      have := nab_eq_nbc_ncb a c b hac hab (Ne.symm hbc) hu hIIA rfl rfl rfl
      simp_all
  -- x = b, y ≠ c, n_cb = n_ab
  . have := nab_dictate_bc c b y (Ne.symm hbc) (Ne.symm hyc) hxy hu hIIA rfl
    simp_all
  -- x = b, y = c
  . exact nab_dictate_bc a b c hab hac hbc hu hIIA hnab

-- ANCHOR: Impossibility
/-- **Arrow's Impossibility Theorem**: No SWF with ≥3 alternatives and ≥1 voters
    can satisfy Unanimity, IIA, and Non-Dictatorship simultaneously. -/
public theorem Impossibility [Fintype α] (ha : Fintype.card α ≥ 3):
    ¬ ∃ R : SWF α N, (Unanimity R) ∧ (IIA R) ∧ (NonDictatorship R) := by
-- ANCHOR_END: Impossibility
  by_contra ⟨ R, ⟨ hu, hIIA, hNonDictator ⟩⟩
  apply hNonDictator
  obtain ⟨ a, b, c, ⟨ hab, hac, hbc⟩ ⟩ := Fintype.two_lt_card_iff.mp ha
  use pivoter a b hab hu
  intro x y hxy
  exact nab_dictate_xy a b c x y hab hac hbc hxy hu hIIA rfl

omit [NeZero N] in
/-- Public elimination rule for the upstream unanimity definition. Atlas addition. -/
public theorem unanimity_iff (R : SWF α N) :
    Unanimity R ↔
      ∀ profile a b,
        (∀ voter, Preorder'.lt (profile voter) b a) →
        Preorder'.lt (R profile) b a :=
  Iff.rfl

omit [NeZero N] in
/-- Public elimination rule for the upstream IIA definition. Atlas addition. -/
public theorem iia_iff (R : SWF α N) :
    IIA R ↔
      ∀ profile₁ profile₂ a b,
        (∀ voter,
          ((profile₁ voter).le b a ↔ (profile₂ voter).le b a) ∧
          ((profile₁ voter).le a b ↔ (profile₂ voter).le a b)) →
        (((R profile₁).le b a ↔ (R profile₂).le b a) ∧
          ((R profile₁).le a b ↔ (R profile₂).le a b)) :=
  Iff.rfl

omit [NeZero N] in
/-- Public elimination rule for non-dictatorship. Atlas addition. -/
public theorem nonDictatorship_iff (R : SWF α N) :
    NonDictatorship R ↔
      ¬ ∃ dictator : Fin N, ∀ a b,
        a ≠ b → ∀ profile,
          Preorder'.lt (profile dictator) b a →
          Preorder'.lt (R profile) b a :=
  Iff.rfl

end

end AISafetyAtlas.Upstream.Arrow
