module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Value reinforcement learning, and why a consistency-preserving agent has no
wireheading incentive

Everitt and Hutter, *Avoiding Wireheading with Value Reinforcement Learning*,
arXiv:1605.03143v1 (10 May 2016), §3–§5. Published as AGI 2016, LNCS 9782,
pp. 12–22; **only the arXiv version has been read**, and every statement number
below is that version's.

The single-step decision problem of §3–§4 is transcribed in full:

* `Beliefs` carries the agent's two belief distributions — `B(s ∣ a)` and
  `B(r ∣ s)` — together with the utility prior `C(u)` and the class `𝒰` itself.
* `condReward`, `marginalReward` and `posterior` are Definition 3: the
  indicator `C(ř ∣ s,u) = ⟦u(s) = ř⟧`, the marginal `C(r ∣ s) = ∑_{u'} C(u')
  C(r ∣ s,u')`, and the utility posterior of equation (1).
* `IsCP` is Definition 5, `IsEEP` is Definition 12.
* `rlValue`/`IsRLAction`, `utilityValue`/`IsUtilityAction` and `vrlValue` are
  Definitions 7, 8 and 9.
* `IsUVRLAction` and `IsCPVRLAction` are Definitions 10 and 11.
* `isEEP_of_isCP` is Lemma 13, `vrlValue_of_isEEP` and `vrlValue_of_isCP` are
  Theorem 14, and `posterior_expectation` is the computation Lemma 27 rests on.

## What the atlas adds to the printed argument

Nothing mathematical. The proofs are the source's, carried out at the source's
own quantifiers. What is new is that the division in equation (1) is handled
rather than assumed away: see the next section.

## Interpretive choices, all of them

* **No finiteness on `𝒮`, `ℛ` or `𝒰` — closed 2026-09-13.** Print's setup
  sentence on p. 4 reads: *"We also assume that `ℛ`, `𝒮`, and `𝒰` are finite or
  countable. Finally, to ensure well-defined expectations, we assume that `ℛ` is
  bounded if it is countable."* Every sum here used to be a `Finset` sum over a
  `Fintype`, which is strictly stronger, and that narrowed Definitions 3, 9 and
  12 and Lemma 13 and Theorem 14 with them. An earlier version of this paragraph
  asserted that "print's `S` and `R` are finite already"; the setup page says
  otherwise and the claim is withdrawn.

  The sums are now unconditional. Nothing was added to `Beliefs`: the two facts
  print's setup supplies — that `C` is summable, and that the joint families
  whose sums Theorem 14 exchanges are summable — are hypotheses of the results
  that need them, and of no others. At a `Fintype` every one of them is
  `Summable.of_finite`, so the signatures this module carried before today are
  instances of these; the worked model in `Examples` discharges them that way.

  **What this does not prove, and the grades rest on it.** `∑'` is `0` by
  convention at a family that is not summable, so where print's boundedness
  fails this module still states something and it is not print's equation. The
  exchange hypothesis is stated as summability of the joint family rather than
  derived from print's countability and boundedness; **that derivation is not
  formalized in this tree**.
* **Utility functions are indexed, not extensional.** `Utility` is an index
  type with `eval : Utility → State → Reward`; two indices may evaluate alike.
  Print's `𝒰` is a set of functions. The difference is invisible to every
  statement here — each one quantifies over `u` and uses only `eval u` and
  `utilityPrior u` — but a *cardinality* claim about `𝒰`, which nothing here
  makes, would not transfer.
* **`B ≥ 0` and `C ≥ 0` are used, and print only calls them distributions.**
  `state_nonneg` closes the branch of Theorem 14 where an action cannot reach a
  state: Definitions 5 and 12 guard on `B(s ∣ a) > 0`, and without
  nonnegativity a *negative* `B(s ∣ a)` would be neither guarded nor zero. `prior_nonneg` is a
  field. It is not decoration: equation (1) divides by `C(r ∣ s)`, Lean's
  division by zero is `0`, and without nonnegativity a state–reward pair with
  `C(r ∣ s) = 0` but `C(u) C(r ∣ s,u) ≠ 0` would falsify Lemma 13 in Lean while
  being unreachable in print's intended reading. With `prior_nonneg`,
  `C(r ∣ s) = 0` forces every summand to vanish and the printed proof goes
  through unchanged, with no side condition on the statement. Normalisation of
  `C` is *not* assumed anywhere, because no proof here needs it.
* **`R` has decidable equality.** Needed to write `⟦u(s) = ř⟧` as a function.
  Print's `R` is a finite or countable set of reals, and this is the only
  structure on it this module asks for.
* **The reward carrier is abstract and `rewardVal` is arbitrary — a widening.**
  Print's `R` *is* a bounded subset of `[0,1] ⊂ ℝ`, so its `u(s)` is a real
  through the identity inclusion: injective, and bounded in `[0,1]`.
  `Beliefs.rewardVal` is an arbitrary map, so two rewards may share a real value
  and values may leave `[0,1]`. No proof here uses either property, so this
  widens every statement rather than narrowing it. It is safe for a further
  reason worth stating: `condReward` compares `eval u s` with `r` **at the
  carrier**, not through `rewardVal`, so the indicator behaves as print's even
  when `rewardVal` collapses two rewards.
* **The quantifier in Definition 5.** Print displays `B(s ∣ a) > 0 ⟹
  B(r ∣ s) = C(r ∣ s)` with `s` free and prefixes "for all `r ∈ R`". Lemma 13's
  proof reads it back as "`B(r ∣ s) = C(r ∣ s)` for all `s` with `B(s ∣ a) > 0`",
  so both variables are universally quantified; `IsCP` quantifies both.

## Explicit non-claims

* **One decision step, no sequential agent.** Print's §4 value functions are
  themselves single-step (`V(a) = ∑_{s,r,u} …`); the sequential reading is
  carried by its examples and by §6–§7. Nothing here iterates.
* **Not Definition 2** (self-delusion types), **not Assumption 4**
  (consistency of `B` and `C`), **not Assumption 15**, and none of the
  appendix results — Definitions 17/21/26, Lemma 20, Theorems 22/25,
  Corollary 24. `IsCP` is stated, and Assumption 6 (`A^CP ≠ ∅`) appears only as
  a hypothesis where it is needed, never as a standing axiom.
* **No existence claim for `A^CP`.** Assumption 6 is print's assumption, not a
  theorem; `AISafetyAtlas.Examples.Wireheading.ValueLearning` exhibits a model
  in which it holds, and one in which a non-CP action strictly beats every CP
  action, so neither `IsCP` nor its negation is vacuous here.
* **Not a claim that CP-VRL is safe.** Theorem 14 says the CP-VRL agent's value
  function does not depend on the reward evidence. Print itself calls the
  robust specification of `C(u)` consistent with `B(r ∣ s)` an open question
  (its Table 1 caption).

Landscape entry: `LAND-VRL-001`. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Wireheading.ValueLearning

variable {State Action Reward Utility : Type*}

/--
The single-step belief state of a value-learning agent, as Everitt and Hutter
set it up in §3.

`stateGiven` is `B(s ∣ a)`, `rewardGiven` is `B(r ∣ s)`, `utilityPrior` is
`C(u)`, and `eval` is the utility function `u` itself, so `rewardVal (eval u s)`
is the real number print writes `u(s)`.
-/
public structure Beliefs (State Action Reward Utility : Type*) where
  /-- `B(s ∣ a)`: the agent's belief in reaching state `s` after action `a`. -/
  stateGiven : Action → State → ℝ
  /-- A belief is nonnegative. Print's `B` is a probability distribution; this
  is the only part of that used, and it is what closes the unreachable-state
  branch of Theorem 14. -/
  state_nonneg : ∀ a s, 0 ≤ stateGiven a s
  /-- `B(r ∣ s)`: the agent's belief in observing reward `r` in state `s`. -/
  rewardGiven : State → Reward → ℝ
  /-- `C(u)`: the prior over the utility class `𝒰`. -/
  utilityPrior : Utility → ℝ
  /-- A prior is nonnegative. Print says "prior"; this is what it buys. -/
  prior_nonneg : ∀ u, 0 ≤ utilityPrior u
  /-- The utility function `u : S → R` named by an index. -/
  eval : Utility → State → Reward
  /-- `R ⊂ [0,1] ⊂ ℝ`: the reward carrier sits in the reals. -/
  rewardVal : Reward → ℝ

/--
Exchanging two unconditional sums needs the joint family summable; the two
marginal summabilities `Summable.tsum_comm'` also asks for follow from it over
`ℝ`, so the results below carry one hypothesis rather than three.
-/
private theorem tsum_comm_of_uncurry {β γ : Type*} {f : β → γ → ℝ}
    (h : Summable (Function.uncurry f)) :
    ∑' (b : β) (c : γ), f b c = ∑' (c : γ) (b : β), f b c :=
  (h.tsum_comm' (fun b => h.prod_factor b)
    (fun c => h.prod_symm.prod_factor c)).symm

namespace Beliefs

variable [DecidableEq Reward]
variable (M : Beliefs State Action Reward Utility)

/-! ## Definition 3: the utility distribution -/

/--
`C(ř ∣ s,u) = ⟦u(s) = ř⟧` (Definition 3).

The inner reward is the utility of the state, with certainty.
-/
@[expose] public def condReward (u : Utility) (s : State) (r : Reward) : ℝ :=
  if M.eval u s = r then 1 else 0

/-- `C(r ∣ s) = ∑_{u'} C(u') C(r ∣ s,u')` (Definition 3, displayed after
equation (1)). -/
@[expose] public noncomputable def marginalReward (s : State) (r : Reward) : ℝ :=
  ∑' u : Utility, M.utilityPrior u * M.condReward u s r

/-- The utility posterior of equation (1),
`C(u ∣ s,r) = C(u) C(r ∣ s,u) / C(r ∣ s)`. -/
@[expose] public noncomputable def posterior (u : Utility) (s : State) (r : Reward) : ℝ :=
  M.utilityPrior u * M.condReward u s r / M.marginalReward s r

/-! ### Behaviour of the transcribed definitions

Three small lemmas pinning `condReward` and `marginalReward` down, so that a
reader can see what they do without unfolding a proof.
-/

/-- The indicator is a probability mass function in `r`: it sums to one. -/
public theorem sum_condReward (u : Utility) (s : State) :
    ∑' r : Reward, M.condReward u s r = 1 := by
  simp only [condReward, eq_comm (a := M.eval u s)]
  exact tsum_ite_eq (M.eval u s) (fun _ => (1 : ℝ))

/-- `C(r ∣ s)` is nonnegative, which is what makes the zero case of equation (1)
harmless. -/
public theorem marginalReward_nonneg (s : State) (r : Reward) :
    0 ≤ M.marginalReward s r := by
  refine tsum_nonneg fun u => mul_nonneg (M.prior_nonneg u) ?_
  unfold condReward
  split <;> norm_num

/--
Each summand of `C(r ∣ s)` is the prior at that index times an indicator, so it
is dominated by the prior and inherits its summability.

This is what a `Fintype Utility` used to supply for free.  Print supplies it
instead: its `𝒰` is finite **or countable** and its `C` is a prior over it.
-/
public theorem summable_prior_mul_condReward (hsum : Summable M.utilityPrior)
    (s : State) (r : Reward) :
    Summable fun u : Utility => M.utilityPrior u * M.condReward u s r := by
  refine Summable.of_nonneg_of_le (fun u => ?_) (fun u => ?_) hsum
  · exact mul_nonneg (M.prior_nonneg u) (by unfold condReward; split <;> norm_num)
  · have hle : M.condReward u s r ≤ 1 := by unfold condReward; split <;> norm_num
    calc M.utilityPrior u * M.condReward u s r
        ≤ M.utilityPrior u * 1 := by
          exact mul_le_mul_of_nonneg_left hle (M.prior_nonneg u)
      _ = M.utilityPrior u := mul_one _

/--
Every summand of `C(r ∣ s)` is dominated by it.

This is the lemma that removes the division hazard: when `C(r ∣ s) = 0`, each
`C(u) C(r ∣ s,u)` is squeezed to `0` as well.
-/
public theorem prior_mul_condReward_le_marginal (hsum : Summable M.utilityPrior)
    (u : Utility) (s : State) (r : Reward) :
    M.utilityPrior u * M.condReward u s r ≤ M.marginalReward s r := by
  refine (M.summable_prior_mul_condReward hsum s r).le_tsum u fun v _ => ?_
  exact mul_nonneg (M.prior_nonneg v) (by unfold condReward; split <;> norm_num)

/-- The consequence used throughout: a vanishing marginal kills every numerator
in equation (1). -/
public theorem prior_mul_condReward_eq_zero_of_marginal_eq_zero
    (hsum : Summable M.utilityPrior)
    {s : State} {r : Reward} (hzero : M.marginalReward s r = 0) (u : Utility) :
    M.utilityPrior u * M.condReward u s r = 0 := by
  have hle := M.prior_mul_condReward_le_marginal hsum u s r
  have hnonneg : 0 ≤ M.utilityPrior u * M.condReward u s r := by
    refine mul_nonneg (M.prior_nonneg u) ?_
    unfold condReward
    split <;> norm_num
  rw [hzero] at hle
  linarith

/-! ## Definitions 5 and 12: the two action properties -/

/--
**Definition 5 (CP actions).** An action is *consistency preserving* when, at
every state it can reach, the agent's reward belief agrees with the reward
marginal induced by its utility prior.
-/
@[expose] public def IsCP (a : Action) : Prop :=
  ∀ s r, 0 < M.stateGiven a s → M.rewardGiven s r = M.marginalReward s r

/--
**Definition 12 (EEP).** An action is *expected ethics preserving* when the
expected posterior equals the prior, at every state the action can reach.
-/
@[expose] public def IsEEP (a : Action) : Prop :=
  ∀ u s, 0 < M.stateGiven a s →
    M.utilityPrior u = ∑' r : Reward, M.rewardGiven s r * M.posterior u s r

/-! ## Definitions 7 to 11: the four agents -/

/-- **Definition 7 (RL agent).** `V^RL(a) = ∑_{s,r} B(s ∣ a) B(r ∣ s) r`. -/
@[expose] public noncomputable def rlValue (a : Action) : ℝ :=
  ∑' s : State, ∑' r : Reward,
    M.stateGiven a s * M.rewardGiven s r * M.rewardVal r

/-- **Definition 7 (RL agent).** The RL agent maximises `V^RL` over all of `A`. -/
@[expose] public def IsRLAction (a : Action) : Prop :=
  ∀ b : Action, M.rlValue b ≤ M.rlValue a

/-- **Definition 8 (utility agent).** `V_u(a) = ∑_s B(s ∣ a) u(s)`. -/
@[expose] public noncomputable def utilityValue (u : Utility) (a : Action) : ℝ :=
  ∑' s : State, M.stateGiven a s * M.rewardVal (M.eval u s)

/-- **Definition 8 (utility agent).** The utility-`u` agent maximises `V_u` over
all of `A`. -/
@[expose] public def IsUtilityAction (u : Utility) (a : Action) : Prop :=
  ∀ b : Action, M.utilityValue u b ≤ M.utilityValue u a

/-- **Definition 9 (VRL value functions).**
`V(a) = ∑_{s,r,u} B(s ∣ a) B(r ∣ s) C(u ∣ s,r) u(s)`. -/
@[expose] public noncomputable def vrlValue (a : Action) : ℝ :=
  ∑' s : State, ∑' r : Reward, ∑' u : Utility,
    M.stateGiven a s * M.rewardGiven s r * M.posterior u s r *
      M.rewardVal (M.eval u s)

/-- **Definition 10 (U-VRL agent).** The unconstrained agent maximises the VRL
value over all of `A`. -/
@[expose] public def IsUVRLAction (a : Action) : Prop :=
  ∀ b : Action, M.vrlValue b ≤ M.vrlValue a

/-- **Definition 11 (CP-VRL agent).** The consistency-preserving agent maximises
the VRL value over `A^CP` — and is itself CP. -/
@[expose] public def IsCPVRLAction (a : Action) : Prop :=
  M.IsCP a ∧ ∀ b : Action, M.IsCP b → M.vrlValue b ≤ M.vrlValue a

/-! ## Lemma 13 and Theorem 14 -/

/--
**Lemma 13 (CP and EEP).** Any CP action is EEP.

Print's proof, unchanged: substitute `B(r ∣ s) = C(r ∣ s)` into the expected
posterior, cancel the marginal, and marginalise `r` out of
`∑_r C(u) C(r ∣ s,u) = C(u)`. The cancellation is performed by cases on whether
`C(r ∣ s)` vanishes; in the vanishing case
`prior_mul_condReward_eq_zero_of_marginal_eq_zero` makes both sides `0`.
-/
public theorem isEEP_of_isCP (hsum : Summable M.utilityPrior) {a : Action}
    (hcp : M.IsCP a) : M.IsEEP a := by
  intro u s hs
  have hterm : ∀ r : Reward,
      M.rewardGiven s r * M.posterior u s r =
        M.utilityPrior u * M.condReward u s r := by
    intro r
    rw [hcp s r hs]
    unfold posterior
    rcases eq_or_ne (M.marginalReward s r) 0 with hzero | hne
    · rw [hzero, M.prior_mul_condReward_eq_zero_of_marginal_eq_zero hsum hzero u]
      simp
    · field_simp
  calc M.utilityPrior u
      = M.utilityPrior u * ∑' r : Reward, M.condReward u s r := by
        rw [M.sum_condReward u s, mul_one]
    _ = ∑' r : Reward, M.utilityPrior u * M.condReward u s r :=
        (tsum_mul_left).symm
    _ = ∑' r : Reward, M.rewardGiven s r * M.posterior u s r :=
        tsum_congr fun r => (hterm r).symm

/--
**Theorem 14 (No wireheading), the EEP form.**

For an EEP action the VRL value function collapses to
`V(a) = ∑_{s,u} B(s ∣ a) C(u) u(s)` — the reward evidence `B(r ∣ s)` has
disappeared, so no choice among EEP actions can be motivated by what the reward
channel would report.
-/
public theorem vrlValue_of_isEEP {a : Action}
    (hexch : ∀ s : State, Summable (Function.uncurry fun (r : Reward) (u : Utility) =>
      M.rewardGiven s r * M.posterior u s r * M.rewardVal (M.eval u s)))
    (heep : M.IsEEP a) :
    M.vrlValue a =
      ∑' s : State, ∑' u : Utility,
        M.stateGiven a s * M.utilityPrior u * M.rewardVal (M.eval u s) := by
  unfold vrlValue
  refine tsum_congr fun s => ?_
  have hpull : ∀ r : Reward,
      (∑' u : Utility, M.stateGiven a s * M.rewardGiven s r * M.posterior u s r *
          M.rewardVal (M.eval u s))
        = M.stateGiven a s *
            ∑' u : Utility, M.rewardGiven s r * M.posterior u s r *
              M.rewardVal (M.eval u s) := by
    intro r
    rw [← tsum_mul_left]
    exact tsum_congr fun u => by ring
  rw [tsum_congr hpull, tsum_mul_left, tsum_comm_of_uncurry (hexch s)]
  rcases eq_or_lt_of_le (M.state_nonneg a s) with hzero | hpos
  · rw [← hzero]
    simp
  · rw [← tsum_mul_left]
    refine tsum_congr fun u => ?_
    have hfac : (∑' r : Reward, M.rewardGiven s r * M.posterior u s r *
          M.rewardVal (M.eval u s))
        = (∑' r : Reward, M.rewardGiven s r * M.posterior u s r) *
            M.rewardVal (M.eval u s) := by
      rw [← tsum_mul_right]
    rw [hfac, ← heep u s hpos]
    ring

/--
**Theorem 14 (No wireheading).** For a CP action — in particular for the action
a CP-VRL agent takes — the value function reduces to equation (5).
-/
public theorem vrlValue_of_isCP (hsum : Summable M.utilityPrior) {a : Action}
    (hexch : ∀ s : State, Summable (Function.uncurry fun (r : Reward) (u : Utility) =>
      M.rewardGiven s r * M.posterior u s r * M.rewardVal (M.eval u s)))
    (hcp : M.IsCP a) :
    M.vrlValue a =
      ∑' s : State, ∑' u : Utility,
        M.stateGiven a s * M.utilityPrior u * M.rewardVal (M.eval u s) :=
  M.vrlValue_of_isEEP hexch (M.isEEP_of_isCP hsum hcp)

/--
The CP-VRL agent's value is a prior-weighted mixture of the utility agents'
values (Definitions 8 and 11 together with Theorem 14).

Print does not display this; it is Theorem 14's right-hand side with the sums
exchanged, and it is what makes "the CP-VRL agent is a utility agent under the
prior" precise.
-/
public theorem vrlValue_eq_prior_mixture (hsum : Summable M.utilityPrior)
    {a : Action}
    (hexch : ∀ s : State, Summable (Function.uncurry fun (r : Reward) (u : Utility) =>
      M.rewardGiven s r * M.posterior u s r * M.rewardVal (M.eval u s)))
    (hmix : Summable (Function.uncurry fun (s : State) (u : Utility) =>
      M.stateGiven a s * M.utilityPrior u * M.rewardVal (M.eval u s)))
    (hcp : M.IsCP a) :
    M.vrlValue a = ∑' u : Utility, M.utilityPrior u * M.utilityValue u a := by
  rw [M.vrlValue_of_isCP hsum hexch hcp, tsum_comm_of_uncurry hmix]
  refine tsum_congr fun u => ?_
  unfold utilityValue
  rw [← tsum_mul_left]
  exact tsum_congr fun s => by ring

/-! ## The computation behind Lemma 27 -/

/--
The posterior expectation of the utility of the current state is the observed
reward itself.

This is the step Appendix C's Lemma 27 turns into `V(a) = V^RL(a)`, and it is
why print says the *unconstrained* VRL agent is no better than the RL agent.
The hypothesis `C(r ∣ s) ≠ 0` is print's own implicit one: equation (1) divides
by it.
-/
public theorem posterior_expectation {s : State} {r : Reward}
    (hne : M.marginalReward s r ≠ 0) :
    ∑' u : Utility, M.posterior u s r * M.rewardVal (M.eval u s) =
      M.rewardVal r := by
  have hterm : ∀ u : Utility,
      M.posterior u s r * M.rewardVal (M.eval u s) =
        (M.utilityPrior u * M.condReward u s r) * M.rewardVal r /
          M.marginalReward s r := by
    intro u
    unfold posterior condReward
    by_cases hu : M.eval u s = r
    · rw [hu]
      simp [div_mul_eq_mul_div]
    · simp [hu]
  rw [tsum_congr hterm, tsum_div_const, tsum_mul_right]
  rw [show ∑' u : Utility, M.utilityPrior u * M.condReward u s r
      = M.marginalReward s r from rfl]
  field_simp

/--
**Lemma 27 (U-VRL is RL), under the support condition.**

Wherever the agent's reward belief is not already zero, the VRL value of an
action agrees with its RL value. The unconstrained VRL agent therefore has
exactly the RL agent's incentives — which is the contrast Theorem 14 is stated
against.

The hypothesis is the support condition print leaves implicit, and it is guarded
by reachability exactly as Definitions 5 and 12 are: it is required only at
states the action can actually reach. `vrlValue_eq_rlValue_of_isCP` discharges
it for a consistency-preserving action, which is the composition that makes the
contrast with Theorem 14 precise.
-/
public theorem vrlValue_eq_rlValue {a : Action}
    (hsupp : ∀ s r, 0 < M.stateGiven a s → M.rewardGiven s r ≠ 0 →
      M.marginalReward s r ≠ 0) :
    M.vrlValue a = M.rlValue a := by
  unfold vrlValue rlValue
  refine tsum_congr fun s => tsum_congr fun r => ?_
  rcases eq_or_lt_of_le (M.state_nonneg a s) with hzero | hpos
  · rw [← hzero]
    simp
  by_cases hr : M.rewardGiven s r = 0
  · simp [hr]
  · have hfac : (∑' u : Utility,
        M.stateGiven a s * M.rewardGiven s r * M.posterior u s r *
            M.rewardVal (M.eval u s))
        = (M.stateGiven a s * M.rewardGiven s r) *
            ∑' u : Utility, M.posterior u s r * M.rewardVal (M.eval u s) := by
      rw [← tsum_mul_left]
      exact tsum_congr fun u => by ring
    rw [hfac, M.posterior_expectation (hsupp s r hpos hr)]

/-- A CP action satisfies the support condition of `vrlValue_eq_rlValue` at
every state it can reach. -/
public theorem support_of_isCP {a : Action} (hcp : M.IsCP a) (s : State)
    (r : Reward) (hs : 0 < M.stateGiven a s) (hr : M.rewardGiven s r ≠ 0) :
    M.marginalReward s r ≠ 0 := by
  rw [hcp s r hs] at hr
  exact hr

/--
**The contrast, composed.** For a consistency-preserving action the VRL value
is the RL value — and by Theorem 14 it is also the prior-weighted expected
utility with the reward evidence gone. The two readings are consistent because
consistency preservation is exactly the condition under which the evidence
carries no information the prior does not already have.
-/
public theorem vrlValue_eq_rlValue_of_isCP {a : Action} (hcp : M.IsCP a) :
    M.vrlValue a = M.rlValue a :=
  M.vrlValue_eq_rlValue (fun s r hs hr => M.support_of_isCP hcp s r hs hr)

end Beliefs
end AISafetyAtlas.Wireheading.ValueLearning
