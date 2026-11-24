module

public import AISafetyAtlas.Preference.DescribedComplexity
import Mathlib.Tactic.Linarith

/-!
# The §5.1 degenerate pairs at exact rational reward codes

Armstrong and Mindermann (§5.1, am-lower-bound, PDF p. 5) claim (1) that
K(π̇) is a lower bound, up to a constant, on K(p, R) for every pair
compatible with π̇, and (2) that the three degenerate pairs (p_π̇, 0),
(p_g, R_π̇) and (−p_g, −R_π̇) are themselves within constants of that bound.
`AISafetyAtlas.Preference.plainKPolicy_le_plainKPair_of_compatible` proves (1) under approximation
codes, where an argmax is not computable and the two greedy pairs have no
description. This module reads planner complexity with **exact rational reward
tables** (the author's ruling R16 (a)) and proves both claims.

## The codings

* `ExactCodesReward` r R: r's program returns, on (s, a, n), the code of a
  rational equal to R s a, for every precision n. An exact code is an
  approximation code (`ExactCodesReward.codesReward`), so one program reads both.
* `DescribesExact` (ruling R16 (a)): the reward slot is an exact code and the
  program is the planner on every exact code. A pair whose reward takes an
  irrational value has no such description, and `plainKPairExact` is ⊤ there.
* `DescribesHybrid`: the reward slot is any approximation code (as in
  `Describes`, so every computable reward has one, irrational values included),
  and the program is the planner on every exact code **and** on the slot itself.
  Every `Describes` and every `DescribesExact` string is a `DescribesHybrid`
  string, so `plainKPairHybrid` is below both (`plainKPairHybrid_le_plainKPair`,
  `plainKPairHybrid_le_plainKPairExact`), and claim (1) for it
  (`plainKPolicy_le_plainKPairHybrid_of_compatible`) gives claim (1) for both.

The hybrid relation is a reading beyond ruling R16 (a): a hybrid description
fixes the planner on every rational table and at the pair's own reward, not at
other irrational rewards. Under R16 (a) alone (`plainKPairExact`), claim (1) is
trivially true (its right side is ⊤) at pairs whose reward takes an irrational
value, and such pairs drop out of claim (2)'s comparison class; the hybrid
statements are the ones with content there.

## The greedy planner

Print gives no tie rule for the argmax of p_g (a recorded silence, PDF p. 5).
`greedyOn` a₀ l takes, at each state, the first maximiser along the listing
a₀ :: l of the actions; it is a maximiser whenever the listing covers the
action type (`greedyOn_max`), and every listing is allowed, so every fixed tie
order is covered. `AISafetyAtlas.Preference.greedyPlanner` picks its maximiser
by choice and no program can be shown to reproduce its ties; at R_π̇ both
return π̇ (`greedyOn_rewardOf`, `AISafetyAtlas.Preference.greedy_rewardOf`).

## What is proved

* `plainKPolicy_le_plainKPairHybrid_of_compatible`,
  `plainKPolicy_le_plainKPairExact_of_compatible`: claim (1).
* `plainKPairExact_degenerate_le`: the three degenerate pairs have exact
  descriptions computable from any code of π̇, so their complexity is at most
  K(π̇) plus one constant.
* `degenerate_near_minimal_exact`, `degenerate_near_minimal_hybrid`: claim (2)
  under each coding. One constant, fixed before π̇, puts each degenerate pair
  within it of K(π̇) in both directions and within it of every pair
  compatible with π̇.

The rational arithmetic on codes is done on ℕ through the Encodable ℚ
encoding, so no Primcodable ℚ instance is needed (the pinned Mathlib has
none).
-/

namespace AISafetyAtlas.Preference

open Kolmogorov
open Nat.Partrec (Code)

/-! ## Comparing rationals through their codes -/

/-- The nonnegative part of the integer coded by z. -/
private def encPos (z : ℕ) : ℕ := bif Nat.bodd z then 0 else Nat.div2 z

/-- The nonpositive part (negated) of the integer coded by z. -/
private def encNeg (z : ℕ) : ℕ := bif Nat.bodd z then Nat.div2 z + 1 else 0

private theorem encPos_sub_encNeg (z : ℤ) :
    ((encPos (Encodable.encode z) : ℤ) - encNeg (Encodable.encode z)) = z := by
  cases z with
  | ofNat n =>
    have : Encodable.encode (Int.ofNat n) = 2 * n := by
      show Function.uncurry Nat.bit (false, n) = 2 * n
      simp [Nat.bit]
    rw [this]
    simp [encPos, encNeg, Nat.div2_val]
  | negSucc n =>
    have : Encodable.encode (Int.negSucc n) = 2 * n + 1 := by
      simp [Encodable.encode, Equiv.intEquivNat, Equiv.intEquivNatSumNat,
        Equiv.natSumNatEquivNat, Equiv.boolProdNatEquivNat]
    simp [encPos, encNeg, this, Nat.div2_val]
    omega

/-- ≤ on rationals, read off their codes. -/
private def ratLe (e₁ e₂ : ℕ) : Bool :=
  decide (encPos e₁.unpair.1 * e₂.unpair.2 + encNeg e₂.unpair.1 * e₁.unpair.2 ≤
    encPos e₂.unpair.1 * e₁.unpair.2 + encNeg e₁.unpair.1 * e₂.unpair.2)

private theorem ratLe_encode (q₁ q₂ : ℚ) :
    ratLe (Encodable.encode q₁) (Encodable.encode q₂) = decide (q₁ ≤ q₂) := by
  have e₁ : Encodable.encode q₁ = Nat.pair (Encodable.encode q₁.num) q₁.den := rfl
  have e₂ : Encodable.encode q₂ = Nat.pair (Encodable.encode q₂.num) q₂.den := rfl
  have h₁ := encPos_sub_encNeg q₁.num
  have h₂ := encPos_sub_encNeg q₂.num
  rw [ratLe, e₁, e₂, Nat.unpair_pair, Nat.unpair_pair]
  refine decide_eq_decide.mpr ?_
  rw [Rat.le_iff, ← Int.ofNat_le]
  push_cast
  generalize (encPos (Encodable.encode q₁.num) : ℤ) = p₁ at *
  generalize (encPos (Encodable.encode q₂.num) : ℤ) = p₂ at *
  generalize (encNeg (Encodable.encode q₁.num) : ℤ) = n₁ at *
  generalize (encNeg (Encodable.encode q₂.num) : ℤ) = n₂ at *
  rw [← h₁, ← h₂]
  constructor <;> intro h <;> linarith

private theorem primrec_ratLe : Primrec₂ ratLe := by
  have hp : Primrec encPos := Primrec.cond Primrec.nat_bodd (Primrec.const 0) Primrec.nat_div2
  have hn : Primrec encNeg :=
    Primrec.cond Primrec.nat_bodd (Primrec.succ.comp Primrec.nat_div2) (Primrec.const 0)
  have u1 : Primrec fun p : ℕ × ℕ => p.1.unpair := Primrec.unpair.comp Primrec.fst
  have u2 : Primrec fun p : ℕ × ℕ => p.2.unpair := Primrec.unpair.comp Primrec.snd
  refine (Primrec.nat_le.comp ?_ ?_).decide
  · exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (hp.comp (Primrec.fst.comp u1)) (Primrec.snd.comp u2))
      (Primrec.nat_mul.comp (hn.comp (Primrec.fst.comp u2)) (Primrec.snd.comp u1))
  · exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (hp.comp (Primrec.fst.comp u2)) (Primrec.snd.comp u1))
      (Primrec.nat_mul.comp (hn.comp (Primrec.fst.comp u1)) (Primrec.snd.comp u2))

/-! ## The greedy planner with a fixed tie order -/

variable {S A : Type*}

/-- The first maximiser of f along the listing a₀ :: l: a later action
replaces the current one only when it scores strictly higher. -/
@[expose] public noncomputable def firstMax (f : A → ℝ) (a₀ : A) (l : List A) : A :=
  l.foldl (fun acc a => if f acc < f a then a else acc) a₀

private theorem firstMax_spec (f : A → ℝ) (l : List A) :
    ∀ a₀ : A, firstMax f a₀ l ∈ a₀ :: l ∧ ∀ a ∈ a₀ :: l, f a ≤ f (firstMax f a₀ l) := by
  induction l with
  | nil => intro a₀; simp [firstMax]
  | cons b l ih =>
    intro a₀
    have hstep : firstMax f a₀ (b :: l) = firstMax f (if f a₀ < f b then b else a₀) l := rfl
    obtain ⟨hmem, hle⟩ := ih (if f a₀ < f b then b else a₀)
    have hfirst : f a₀ ≤ f (if f a₀ < f b then b else a₀) ∧
        f b ≤ f (if f a₀ < f b then b else a₀) := by
      split_ifs with h
      · exact ⟨h.le, le_rfl⟩
      · exact ⟨le_rfl, not_lt.1 h⟩
    have htop := hle _ (List.mem_cons_self ..)
    rw [hstep]
    refine ⟨?_, fun a ha => ?_⟩
    · rcases List.mem_cons.1 hmem with h | h
      · rw [h]; split_ifs <;> simp
      · simp [h]
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact hfirst.1.trans htop
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hfirst.2.trans htop
      · exact hle a (List.mem_cons_of_mem _ ha)

/-- **A greedy planner with a computable tie order** (the source's p_g, §5.1,
PDF p. 5, *"the greedy planner"*; print gives no tie rule): at each state, the
first reward-maximising action along the listing a₀ :: l. -/
@[expose] public noncomputable def greedyOn (a₀ : A) (l : List A) :
    Planner (RewardFn S A) (Policy S A) :=
  fun R s => firstMax (R s) a₀ l

/-- `greedyOn` is greedy: when the listing covers the actions, no action scores
above its choice. -/
public theorem greedyOn_max {a₀ : A} {l : List A} (hl : ∀ a, a ∈ a₀ :: l)
    (R : RewardFn S A) (s : S) (a : A) : R s a ≤ R s (greedyOn a₀ l R s) :=
  (firstMax_spec (R s) l a₀).2 a (hl a)

/-- Every finite nonempty action type has a listing covering it, so the
covering hypothesis of the theorems below holds at every instance of print's
finite action space. -/
public theorem exists_covering_listing [Fintype A] [Nonempty A] :
    ∃ (a₀ : A) (l : List A), ∀ a, a ∈ a₀ :: l :=
  ⟨Classical.arbitrary A, Finset.univ.toList, fun a =>
    List.mem_cons_of_mem _ (Finset.mem_toList.2 (Finset.mem_univ a))⟩

/-- **p_g(R_π) = π** for the greedy planner with any covering tie order. -/
public theorem greedyOn_rewardOf [DecidableEq A] {a₀ : A} {l : List A}
    (hl : ∀ a, a ∈ a₀ :: l) (π : Policy S A) : greedyOn a₀ l (rewardOf π) = π := by
  funext s
  by_contra hne
  have hmax := greedyOn_max hl (rewardOf π) s (π s)
  have h1 : rewardOf π s (π s) = 1 := by simp [rewardOf]
  have h0 : rewardOf π s (greedyOn a₀ l (rewardOf π) s) = 0 := by simp [rewardOf, hne]
  rw [h1, h0] at hmax
  exact absurd hmax (not_le.mpr zero_lt_one)

/-- **(−p_g)(−R_π) = π** for the greedy planner with any covering tie order. -/
public theorem negPlanner_greedyOn_neg_rewardOf [DecidableEq A] {a₀ : A} {l : List A}
    (hl : ∀ a, a ∈ a₀ :: l) (π : Policy S A) :
    negPlanner (greedyOn a₀ l) (-rewardOf π) = π := by
  rw [negPlanner, neg_neg, greedyOn_rewardOf hl]

/-! ## Exact rational reward codes and the two description relations -/

variable [Encodable S] [Encodable A]

/-- **A string exactly codes a rational reward table**: at every state, action and
precision its program returns the code of the rational equal to the reward. -/
@[expose] public def ExactCodesReward (r : BitString) (R : RewardFn S A) : Prop :=
  ∀ s a, ∃ q : ℚ, (q : ℝ) = R s a ∧
    ∀ n : ℕ, Encodable.encode q ∈ (pairProgram r).eval (Encodable.encode (s, a, n))

/-- An exact code is an approximation code, with error zero. -/
public theorem ExactCodesReward.codesReward {r : BitString} {R : RewardFn S A}
    (h : ExactCodesReward r R) : CodesReward r R := fun s a n => by
  obtain ⟨q, hq, hrun⟩ := h s a
  exact ⟨q, hrun n, by rw [← hq, sub_self, abs_zero]; positivity⟩

/-- **A string describes a pair, with exact rational codes** (ruling R16 (a)): its
reward slot exactly codes the reward, and its program, run on any exact code of
any reward R', returns a code of the policy the planner assigns to R'. -/
@[expose] public def DescribesExact (y : Pair S A) (x : BitString) : Prop :=
  ExactCodesReward (pairReward x) y.2 ∧
    ∀ (r : BitString) (R' : RewardFn S A), ExactCodesReward r R' →
      ∃ b ∈ runOn (pairProgram x) r, CodesPolicy b (y.1 R')

/-- **A string describes a pair, in the hybrid coding**: its reward slot codes the
reward to any precision (irrational values allowed), and its program is the
planner on every exact rational code and on the slot itself. -/
@[expose] public def DescribesHybrid (y : Pair S A) (x : BitString) : Prop :=
  CodesReward (pairReward x) y.2 ∧
    (∀ (r : BitString) (R' : RewardFn S A), ExactCodesReward r R' →
      ∃ b ∈ runOn (pairProgram x) r, CodesPolicy b (y.1 R')) ∧
    ∃ b ∈ runOn (pairProgram x) (pairReward x), CodesPolicy b (y.1 y.2)

variable (S A) in
/-- **K(p, R) with exact rational codes**: ⊤ when no string describes the
pair, in particular when its reward takes an irrational value. -/
@[expose] public noncomputable def plainKPairExact (U : Map) (y : Pair S A) : ENat :=
  sInf (plainK U '' {x | DescribesExact y x})

variable (S A) in
/-- **K(p, R) in the hybrid coding.** -/
@[expose] public noncomputable def plainKPairHybrid (U : Map) (y : Pair S A) : ENat :=
  sInf (plainK U '' {x | DescribesHybrid y x})

/-- An exact description is a hybrid one. -/
public theorem DescribesExact.describesHybrid {y : Pair S A} {x : BitString}
    (h : DescribesExact y x) : DescribesHybrid y x :=
  ⟨h.1.codesReward, h.2, h.2 _ _ h.1⟩

/-- An approximation-code description (`Describes`) is a hybrid one. -/
public theorem Describes.describesHybrid {y : Pair S A} {x : BitString}
    (h : Describes y x) : DescribesHybrid y x :=
  ⟨h.1, fun r R' hr => h.2 r R' hr.codesReward, h.2 _ _ h.1⟩

/-- The hybrid complexity is at most the exact one. -/
public theorem plainKPairHybrid_le_plainKPairExact (U : Map) (y : Pair S A) :
    plainKPairHybrid S A U y ≤ plainKPairExact S A U y :=
  sInf_le_sInf (Set.image_mono fun _ hx => DescribesExact.describesHybrid hx)

/-- The hybrid complexity is at most the approximation-code one. -/
public theorem plainKPairHybrid_le_plainKPair (U : Map) (y : Pair S A) :
    plainKPairHybrid S A U y ≤ plainKPair S A U y :=
  sInf_le_sInf (Set.image_mono fun _ hx => Describes.describesHybrid hx)

/-- A bound by every element of a set of strings bounds its least complexity. -/
private theorem le_sInf_image_add (U : Map) (P : BitString → Prop) {X : ENat} {c : ℕ}
    (h : ∀ x, P x → X ≤ plainK U x + c) : X ≤ sInf (plainK U '' {x | P x}) + c := by
  rcases (plainK U '' {x | P x}).eq_empty_or_nonempty with hE | hE
  · rw [hE, sInf_empty, top_add]
    exact le_top
  · obtain ⟨x, hx, hxK⟩ := csInf_mem hE
    rw [← hxK]
    exact h x hx

/--
**Print's §5.1 claim (1), in the hybrid coding** (Armstrong and Mindermann,
§5.1, am-lower-bound, PDF p. 5: *"the complexity of π̇ is close to a lower
bound on any pair compatible with it"*). One constant, fixed before the pair and
the policy, bounds K(π̇) by K(p, R) for every pair with p(R) = π̇. Every
computable reward has a hybrid code, irrational values included.
-/
public theorem plainKPolicy_le_plainKPairHybrid_of_compatible (U : Map)
    (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (y : Pair S A) (π : Policy S A), ReasonableLanguage.Compatible y π →
      plainKPolicy S A U π ≤ plainKPairHybrid S A U y + (c : ENat) := by
  obtain ⟨c, hc⟩ := behaviour_le_of_evaluatesTo U hU
  refine ⟨c, fun y π h => le_sInf_image_add U _ fun x hx => ?_⟩
  obtain ⟨b, hb, hcode⟩ := hx.2.2
  have h' : y.1 y.2 = π := h
  rw [h'] at hcode
  exact (plainKPolicy_le_of_codesPolicy U hcode).trans (hc x b hb)

/-- **Print's §5.1 claim (1), with exact rational codes** (ruling R16 (a)). -/
public theorem plainKPolicy_le_plainKPairExact_of_compatible (U : Map)
    (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (y : Pair S A) (π : Policy S A), ReasonableLanguage.Compatible y π →
      plainKPolicy S A U π ≤ plainKPairExact S A U y + (c : ENat) := by
  obtain ⟨c, hc⟩ := plainKPolicy_le_plainKPairHybrid_of_compatible (S := S) (A := A) U hU
  refine ⟨c, fun y π h => (hc y π h).trans ?_⟩
  gcongr
  exact plainKPairHybrid_le_plainKPairExact U y

/-! ## The programs -/

/-- Query a reward code at state code es, precision 0, along a list of action
codes. -/
private def queries : List ℕ → Code → ℕ → Part (List (ℕ × ℕ))
  | [], _, _ => Part.some []
  | ea :: L, c, es => (c.eval (Nat.pair es (Nat.pair ea 0))).bind fun v =>
      (queries L c es).map fun t => (ea, v) :: t

private theorem partrec_queries (L : List ℕ) : Partrec₂ (queries L) := by
  induction L with
  | nil => exact Partrec.const' _
  | cons ea L ih =>
    refine Partrec.bind (Code.eval_part.comp Computable.fst
      (Primrec.to_comp (Primrec₂.natPair.comp Primrec.snd
        (Primrec₂.natPair.comp (Primrec.const ea) (Primrec.const 0))))) ?_
    exact Partrec.map (ih.comp (Computable.fst.comp Computable.fst)
        (Computable.snd.comp Computable.fst))
      (Computable.list_cons.comp
        (Computable.pair (Computable.const ea) (Computable.snd.comp Computable.fst))
        Computable.snd).to₂

/-- One step of the first-best fold: maximise (flip = false) or minimise. -/
private def step (flip : Bool) (acc new : ℕ × ℕ) : ℕ × ℕ :=
  cond (bif flip then !ratLe acc.2 new.2 else !ratLe new.2 acc.2) new acc

private theorem primrec_step (flip : Bool) : Primrec₂ (step flip) := by
  have hl : Primrec fun p : (ℕ × ℕ) × (ℕ × ℕ) => ratLe p.1.2 p.2.2 :=
    primrec_ratLe.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have hr : Primrec fun p : (ℕ × ℕ) × (ℕ × ℕ) => ratLe p.2.2 p.1.2 :=
    primrec_ratLe.comp (Primrec.snd.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
  cases flip
  · exact Primrec.cond (Primrec.not.comp hr) Primrec.snd Primrec.fst
  · exact Primrec.cond (Primrec.not.comp hl) Primrec.snd Primrec.fst

/-- The first best action code of a list of (action code, value code) pairs. -/
private def firstBest (flip : Bool) (t : List (ℕ × ℕ)) : ℕ :=
  (t.tail.foldl (step flip) t.headI).1

private theorem primrec_firstBest (flip : Bool) : Primrec (firstBest flip) :=
  Primrec.fst.comp (Primrec.list_foldl Primrec.list_tail
    Primrec.list_headI
    ((primrec_step flip).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)

/-- The greedy computation on ⟨code of a reward program, state code⟩. -/
private def greedyRun (flip : Bool) (L : List ℕ) (n : ℕ) : Part ℕ :=
  (queries L (Denumerable.ofNat Code n.unpair.1) n.unpair.2).map (firstBest flip)

private theorem partrec_greedyRun (flip : Bool) (L : List ℕ) : Nat.Partrec (greedyRun flip L) :=
  Partrec.nat_iff.1 <| Partrec.map
    ((partrec_queries L).comp ((Computable.ofNat Code).comp
        (Computable.fst.comp (Primrec.to_comp Primrec.unpair)))
      (Computable.snd.comp (Primrec.to_comp Primrec.unpair)))
    ((primrec_firstBest flip).to_comp.comp Computable.snd).to₂

/-- The reward-code computation on ⟨code of a policy program, ⟨s, ⟨a, n⟩⟩⟩:
v₁ where the policy plays a at s, v₀ elsewhere. -/
private def indicatorRun (v₁ v₀ : ℕ) (n : ℕ) : Part ℕ :=
  ((Denumerable.ofNat Code n.unpair.1).eval n.unpair.2.unpair.1).map fun e =>
    if e = n.unpair.2.unpair.2.unpair.1 then v₁ else v₀

private theorem partrec_indicatorRun (v₁ v₀ : ℕ) : Nat.Partrec (indicatorRun v₁ v₀) := by
  have hu : Computable fun n : ℕ => n.unpair := Primrec.to_comp Primrec.unpair
  have hea : Primrec fun p : ℕ × ℕ => p.1.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))))
  have hg : Primrec fun p : ℕ × ℕ => if p.2 = p.1.unpair.2.unpair.2.unpair.1 then v₁ else v₀ :=
    Primrec.ite (Primrec.eq.comp Primrec.snd hea) (Primrec.const _) (Primrec.const _)
  exact Partrec.nat_iff.1 (Partrec.map (Code.eval_part.comp
    ((Computable.ofNat Code).comp (Computable.fst.comp hu))
    (Computable.fst.comp (hu.comp (Computable.snd.comp hu)))) hg.to_comp.to₂)

/-- A program with a fixed first argument, as a string: the curried code of g
at the code of r's program. -/
private def curryString (g : Code) (r : BitString) : BitString :=
  pairString (Encodable.encode (Code.curry g (Encodable.encode (pairProgram r)))) []

private theorem eval_pairProgram_curryString (g : Code) (r : BitString) (m : ℕ) :
    (pairProgram (curryString g r)).eval m =
      g.eval (Nat.pair (Encodable.encode (pairProgram r)) m) := by
  rw [curryString, pairProgram_pairString, Denumerable.ofNat_encode, Code.eval_curry]

private theorem primrec_replicate_true' : Primrec fun n : ℕ => List.replicate n true := by
  have h : (fun n : ℕ => List.replicate n true) = fun n => (List.range n).map fun _ => true := by
    funext n
    simp
  rw [h]
  exact Primrec.list_map Primrec.list_range (Primrec.const true).to₂

private theorem primrec_pairString : Primrec₂ pairString :=
  Primrec.list_append.comp (primrec_replicate_true'.comp Primrec.fst)
    (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)

private theorem computable_curryString (g : Code) : Computable (curryString g) :=
  (primrec_pairString.to_comp).comp
    (Computable.encode.comp ((Primrec₂.to_comp Code.primrec₂_curry).comp (Computable.const g)
      (Computable.encode.comp computable_pairProgram)))
    (Computable.const [])

private theorem computable_pairString_left (n : ℕ) : Computable (pairString n) :=
  primrec_pairString.to_comp.comp (Computable.const n) Computable.id

/-- The greedy program's code. -/
private noncomputable def greedyRunCode (flip : Bool) (L : List ℕ) : Code :=
  Classical.choose (Code.exists_code.1 (partrec_greedyRun flip L))

/-- The indicator program's code. -/
private noncomputable def indicatorCode (v₁ v₀ : ℕ) : Code :=
  Classical.choose (Code.exists_code.1 (partrec_indicatorRun v₁ v₀))

private theorem nat_partrec_planner (g : Code) :
    Nat.Partrec fun n => ((Encodable.decode (α := BitString) n).map fun r =>
      Encodable.encode (curryString g r) : Part ℕ) :=
  Partrec.nat_iff.1 (Computable.ofOption (Computable.option_map Computable.decode
    (Computable.encode.comp ((computable_curryString g).comp Computable.snd)).to₂))

/-- The planner program: maps a reward code r to the curried greedy program at
r's program. -/
private noncomputable def plannerCode (flip : Bool) (L : List ℕ) : Code :=
  Classical.choose (Code.exists_code.1 (nat_partrec_planner (greedyRunCode flip L)))

private theorem runOn_plannerCode (flip : Bool) (L : List ℕ) (r : BitString) :
    runOn (plannerCode flip L) r = Part.some (curryString (greedyRunCode flip L) r) := by
  rw [runOn, plannerCode, Classical.choose_spec (Code.exists_code.1 (nat_partrec_planner
    (greedyRunCode flip L)))]
  simp [Encodable.encodek]

private theorem queries_mem {c : Code} {s : S} {q : A → ℚ}
    (hq : ∀ a, Encodable.encode (q a) ∈ c.eval (Encodable.encode (s, a, 0))) :
    ∀ L : List A, (L.map fun a => (Encodable.encode a, Encodable.encode (q a))) ∈
      queries (L.map Encodable.encode) c (Encodable.encode s)
  | [] => Part.mem_some _
  | a :: L => Part.mem_bind_iff.2 ⟨_, hq a, Part.mem_map _ (queries_mem hq L)⟩

private theorem foldl_map_comm {α β : Type*} (g : α → β) (sA : α → α → α) (sN : β → β → β)
    (h : ∀ x y, sN (g x) (g y) = g (sA x y)) :
    ∀ (l : List α) (a₀ : α), (l.map g).foldl sN (g a₀) = g (l.foldl sA a₀)
  | [], _ => rfl
  | b :: l, a₀ => by
    simp only [List.map_cons, List.foldl_cons, h]
    exact foldl_map_comm g sA sN h l _

/-- **The greedy program is the greedy planner on exact codes**: run on an exact
code of R', the planner program returns a code of the first maximiser
(flip = false) or first minimiser (flip = true) of R' along a₀ :: l. -/
private theorem codesPolicy_plannerCode (flip : Bool) (a₀ : A) (l : List A)
    {r : BitString} {R' : RewardFn S A} (hr : ExactCodesReward r R') :
    ∃ b ∈ runOn (plannerCode flip ((a₀ :: l).map Encodable.encode)) r,
      CodesPolicy b (fun s => firstMax (fun a => bif flip then -R' s a else R' s a) a₀ l) := by
  refine ⟨_, by rw [runOn_plannerCode]; exact Part.mem_some _, fun s => ?_⟩
  choose q hq hrun using hr s
  rw [eval_pairProgram_curryString, greedyRunCode,
    Classical.choose_spec (Code.exists_code.1 (partrec_greedyRun _ _)), greedyRun,
    Nat.unpair_pair, Denumerable.ofNat_encode]
  refine Part.mem_map_iff _ |>.2 ⟨_, queries_mem (fun a => hrun a 0) (a₀ :: l), ?_⟩
  have hstep : ∀ x y : A,
      step flip (Encodable.encode x, Encodable.encode (q x)) (Encodable.encode y, Encodable.encode (q y)) =
        (fun a => (Encodable.encode a, Encodable.encode (q a)))
          ((fun acc a => if (fun a => bif flip then -R' s a else R' s a) acc <
            (fun a => bif flip then -R' s a else R' s a) a then a else acc) x y) := by
    intro x y
    simp only [step, ratLe_encode, ← hq]
    cases flip
    · by_cases h : q x < q y
      · simp [h, not_le.2 h]
      · simp [h, not_lt.1 h]
    · by_cases h : q y < q x
      · simp [h, not_le.2 h]
      · simp [h, not_lt.1 h]
  simp only [firstBest, List.map_cons, List.tail_cons, List.headI_cons]
  rw [foldl_map_comm _ _ _ hstep]
  rfl

/-! ## Descriptions of the three degenerate pairs -/

/-- The indicator reward code built from a policy code b. -/
private theorem exactCodesReward_indicator [DecidableEq A] {π : Policy S A} {b : BitString}
    (hb : CodesPolicy b π) (v₁ v₀ : ℚ) :
    ExactCodesReward (curryString (indicatorCode (Encodable.encode v₁) (Encodable.encode v₀)) b)
      (fun s a => if a = π s then (v₁ : ℝ) else v₀) := fun s a => by
  refine ⟨if a = π s then v₁ else v₀, by by_cases h : a = π s <;> simp [h], fun n => ?_⟩
  rw [eval_pairProgram_curryString, indicatorCode,
    Classical.choose_spec (Code.exists_code.1 (partrec_indicatorRun _ _)), indicatorRun]
  have he : Encodable.encode (s, a, n) =
      Nat.pair (Encodable.encode s) (Nat.pair (Encodable.encode a) n) := rfl
  simp only [he, Nat.unpair_pair, Denumerable.ofNat_encode]
  refine Part.mem_map_iff _ |>.2 ⟨_, hb s, ?_⟩
  by_cases h : a = π s
  · simp [h]
  · have : Encodable.encode (π s) ≠ Encodable.encode a := fun he' =>
      h (Encodable.encode_injective he').symm
    simp [h, this]

/-- The fixed exact code of the zero reward. -/
private def zeroCode : BitString :=
  pairString (Encodable.encode (Code.const (Encodable.encode (0 : ℚ)))) []

private theorem exactCodesReward_zeroCode : ExactCodesReward zeroCode (0 : RewardFn S A) :=
  fun _ _ => ⟨0, by simp, fun _ => by
    rw [zeroCode, pairProgram_pairString, Denumerable.ofNat_encode, Code.eval_const]
    exact Part.mem_some _⟩

private theorem describesExact_indifferent {π : Policy S A} {b : BitString}
    (hb : CodesPolicy b π) :
    DescribesExact (indifferentPlanner π, (0 : RewardFn S A)) (degeneratePair zeroCode b) := by
  refine ⟨by rw [degeneratePair, pairReward_pairString]; exact exactCodesReward_zeroCode,
    fun r' R' _ => ⟨b, ?_, hb⟩⟩
  rw [runOn, degeneratePair, pairProgram_pairString, Denumerable.ofNat_encode, Code.eval_const]
  simp [Encodable.encodek]

/-- The description string of a greedy pair: the planner program, then the
indicator reward code built from b. -/
private noncomputable def greedyString (flip : Bool) (a₀ : A) (l : List A) (v₁ : ℚ)
    (b : BitString) : BitString :=
  pairString (Encodable.encode (plannerCode flip ((a₀ :: l).map Encodable.encode)))
    (curryString (indicatorCode (Encodable.encode v₁) (Encodable.encode (0 : ℚ))) b)

private theorem computable_greedyString (flip : Bool) (a₀ : A) (l : List A) (v₁ : ℚ) :
    Computable (greedyString flip a₀ l v₁) :=
  (computable_pairString_left _).comp (computable_curryString _)

private theorem describesExact_greedy [DecidableEq A] (a₀ : A) (l : List A)
    {π : Policy S A} {b : BitString} (hb : CodesPolicy b π) :
    DescribesExact (greedyOn a₀ l, rewardOf π) (greedyString false a₀ l 1 b) := by
  refine ⟨?_, fun r R' hr => ?_⟩
  · rw [greedyString, pairReward_pairString]
    convert exactCodesReward_indicator hb 1 0 using 1
    funext s a
    simp [rewardOf]
  · rw [greedyString, pairProgram_pairString, Denumerable.ofNat_encode]
    exact codesPolicy_plannerCode false a₀ l hr

private theorem describesExact_antigreedy [DecidableEq A] (a₀ : A) (l : List A)
    {π : Policy S A} {b : BitString} (hb : CodesPolicy b π) :
    DescribesExact (negPlanner (greedyOn a₀ l), -rewardOf π) (greedyString true a₀ l (-1) b) := by
  refine ⟨?_, fun r R' hr => ?_⟩
  · rw [greedyString, pairReward_pairString]
    convert exactCodesReward_indicator hb (-1) 0 using 1
    funext s a
    by_cases h : a = π s <;> simp [rewardOf, h]
  · rw [greedyString, pairProgram_pairString, Denumerable.ofNat_encode]
    exact codesPolicy_plannerCode true a₀ l hr

private theorem plainKPairExact_le_of_describesExact (U : Map) {y : Pair S A} {x : BitString}
    (hx : DescribesExact y x) : plainKPairExact S A U y ≤ plainK U x :=
  sInf_le ⟨x, hx, rfl⟩

/-- A computable map sending codes of π to descriptions of d π bounds
K(d π) by K(π) plus a constant. -/
private theorem plainKPairExact_le_of_map (U : Map) (hU : isOptimalConditional U)
    {d : Policy S A → Pair S A} {g : BitString → BitString} (hg : Computable g)
    (hd : ∀ π b, CodesPolicy b π → DescribesExact (d π) (g b)) :
    ∃ c : ℕ, ∀ π, plainKPairExact S A U (d π) ≤ plainKPolicy S A U π + c := by
  obtain ⟨c, hc⟩ := plainKMapLe U hU g hg
  exact ⟨c, fun π => le_sInf_image_add U (fun b => CodesPolicy b π) fun b hb =>
    (plainKPairExact_le_of_describesExact U (hd π b hb)).trans (hc b)⟩

/--
**The three degenerate pairs are cheap** (Armstrong and Mindermann, §5.1,
PDF p. 5: *"we will first produce three degenerate pairs that can be simply
constructed from π̇"*). With exact rational codes, one constant, fixed before
the policy, bounds the complexity of (p_π̇, 0), (p_g, R_π̇) and
(−p_g, −R_π̇) by K(π̇) plus that constant, for the greedy planner with any
tie order a₀ :: l.
-/
public theorem plainKPairExact_degenerate_le [DecidableEq A] (U : Map)
    (hU : isOptimalConditional U) (a₀ : A) (l : List A) :
    ∃ c : ℕ, ∀ π : Policy S A, ∀ d ∈ ({(indifferentPlanner π, 0), (greedyOn a₀ l, rewardOf π),
        (negPlanner (greedyOn a₀ l), -rewardOf π)} : Set (Pair S A)),
      plainKPairExact S A U d ≤ plainKPolicy S A U π + (c : ENat) := by
  obtain ⟨c₁, h₁⟩ := plainKPairExact_le_of_map (d := fun π : Policy S A => ((indifferentPlanner π, 0) : Pair S A))
    U hU (computable_degeneratePair zeroCode) fun _ _ hb => describesExact_indifferent hb
  obtain ⟨c₂, h₂⟩ := plainKPairExact_le_of_map (d := fun π : Policy S A => ((greedyOn a₀ l, rewardOf π) : Pair S A))
    U hU (computable_greedyString false a₀ l 1) fun _ _ hb => describesExact_greedy a₀ l hb
  obtain ⟨c₃, h₃⟩ := plainKPairExact_le_of_map
    (d := fun π : Policy S A => ((negPlanner (greedyOn a₀ l), -rewardOf π) : Pair S A))
    U hU (computable_greedyString true a₀ l (-1)) fun _ _ hb => describesExact_antigreedy a₀ l hb
  refine ⟨max c₁ (max c₂ c₃), fun π d hd => ?_⟩
  have hmono : ∀ {X : ENat} {k : ℕ}, k ≤ max c₁ (max c₂ c₃) →
      X ≤ plainKPolicy S A U π + k → X ≤ plainKPolicy S A U π + (max c₁ (max c₂ c₃) : ℕ) :=
    fun hk hX => hX.trans (by gcongr)
  rcases hd with rfl | rfl | rfl
  · exact hmono (le_max_left _ _) (h₁ π)
  · exact hmono ((le_max_left _ _).trans (le_max_right _ _)) (h₂ π)
  · exact hmono ((le_max_right _ _).trans (le_max_right _ _)) (h₃ π)

omit [Encodable S] [Encodable A] in
/-- The three degenerate pairs are compatible with π when the tie order covers
the actions. -/
private theorem compatible_degenerate [DecidableEq A] {a₀ : A} {l : List A}
    (hl : ∀ a, a ∈ a₀ :: l) (π : Policy S A) :
    ∀ d ∈ ({(indifferentPlanner π, 0), (greedyOn a₀ l, rewardOf π),
        (negPlanner (greedyOn a₀ l), -rewardOf π)} : Set (Pair S A)),
      ReasonableLanguage.Compatible d π := by
  rintro d (rfl | rfl | rfl)
  · rfl
  · exact greedyOn_rewardOf hl π
  · exact negPlanner_greedyOn_neg_rewardOf hl π

/--
**Print's §5.1 claim (2), with exact rational codes** (ruling R16 (a);
Armstrong and Mindermann, §5.1, am-lower-bound, PDF p. 5: *"degenerate
decompositions are themselves close to this bound ... it too will have a
complexity close to the minimal complexity of any other pair compatible with
it"*). For the greedy planner with any tie order listing every action, one
constant c, fixed before the policy, makes each of (p_π̇, 0), (p_g, R_π̇),
(−p_g, −R_π̇) within c of K(π̇) in both directions and within c of every
pair compatible with π̇.
-/
public theorem degenerate_near_minimal_exact [DecidableEq A] (U : Map)
    (hU : isOptimalConditional U) {a₀ : A} {l : List A} (hl : ∀ a, a ∈ a₀ :: l) :
    ∃ c : ℕ, ∀ π : Policy S A, ∀ d ∈ ({(indifferentPlanner π, 0), (greedyOn a₀ l, rewardOf π),
        (negPlanner (greedyOn a₀ l), -rewardOf π)} : Set (Pair S A)),
      plainKPolicy S A U π ≤ plainKPairExact S A U d + (c : ENat) ∧
      plainKPairExact S A U d ≤ plainKPolicy S A U π + (c : ENat) ∧
      ∀ y : Pair S A, ReasonableLanguage.Compatible y π →
        plainKPairExact S A U d ≤ plainKPairExact S A U y + (c : ENat) := by
  obtain ⟨c₀, h₀⟩ := plainKPolicy_le_plainKPairExact_of_compatible (S := S) (A := A) U hU
  obtain ⟨c₁, h₁⟩ := plainKPairExact_degenerate_le (S := S) U hU a₀ l
  refine ⟨c₀ + c₁, fun π d hd => ⟨?_, ?_, fun y hy => ?_⟩⟩
  · exact (h₀ d π (compatible_degenerate hl π d hd)).trans
      (by gcongr; exact Nat.le_add_right _ _)
  · exact (h₁ π d hd).trans (by gcongr; exact Nat.le_add_left _ _)
  · calc plainKPairExact S A U d ≤ plainKPolicy S A U π + c₁ := h₁ π d hd
      _ ≤ plainKPairExact S A U y + c₀ + c₁ := by gcongr; exact h₀ y π hy
      _ = plainKPairExact S A U y + ((c₀ + c₁ : ℕ) : ENat) := by push_cast; rw [add_assoc]

/--
**Print's §5.1 claim (2), in the hybrid coding** (as
`degenerate_near_minimal_exact`, with every computable reward coded, irrational
values included, so the competitors y range over every pair a program
generates).
-/
public theorem degenerate_near_minimal_hybrid [DecidableEq A] (U : Map)
    (hU : isOptimalConditional U) {a₀ : A} {l : List A} (hl : ∀ a, a ∈ a₀ :: l) :
    ∃ c : ℕ, ∀ π : Policy S A, ∀ d ∈ ({(indifferentPlanner π, 0), (greedyOn a₀ l, rewardOf π),
        (negPlanner (greedyOn a₀ l), -rewardOf π)} : Set (Pair S A)),
      plainKPolicy S A U π ≤ plainKPairHybrid S A U d + (c : ENat) ∧
      plainKPairHybrid S A U d ≤ plainKPolicy S A U π + (c : ENat) ∧
      ∀ y : Pair S A, ReasonableLanguage.Compatible y π →
        plainKPairHybrid S A U d ≤ plainKPairHybrid S A U y + (c : ENat) := by
  obtain ⟨c₀, h₀⟩ := plainKPolicy_le_plainKPairHybrid_of_compatible (S := S) (A := A) U hU
  obtain ⟨c₁, h₁⟩ := plainKPairExact_degenerate_le (S := S) U hU a₀ l
  have h₁' : ∀ π, ∀ d ∈ ({(indifferentPlanner π, 0), (greedyOn a₀ l, rewardOf π),
      (negPlanner (greedyOn a₀ l), -rewardOf π)} : Set (Pair S A)),
      plainKPairHybrid S A U d ≤ plainKPolicy S A U π + c₁ := fun π d hd =>
    (plainKPairHybrid_le_plainKPairExact U d).trans (h₁ π d hd)
  refine ⟨c₀ + c₁, fun π d hd => ⟨?_, ?_, fun y hy => ?_⟩⟩
  · exact (h₀ d π (compatible_degenerate hl π d hd)).trans
      (by gcongr; exact Nat.le_add_right _ _)
  · exact (h₁' π d hd).trans (by gcongr; exact Nat.le_add_left _ _)
  · calc plainKPairHybrid S A U d ≤ plainKPolicy S A U π + c₁ := h₁' π d hd
      _ ≤ plainKPairHybrid S A U y + c₀ + c₁ := by gcongr; exact h₀ y π hy
      _ = plainKPairHybrid S A U y + ((c₀ + c₁ : ℕ) : ENat) := by push_cast; rw [add_assoc]

end AISafetyAtlas.Preference
