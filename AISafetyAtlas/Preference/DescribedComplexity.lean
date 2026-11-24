module

public import AISafetyAtlas.Preference.Complexity
public import AISafetyAtlas.Preference.Reasonable
public import Mathlib.Data.Rat.Encodable

/-!
# The §5.1 lower bound at print's planners, rewards and policies

`AISafetyAtlas.Preference.Complexity` proves the source's lower bound
(`behaviour_le_of_evaluatesTo`) for pairs and behaviours that are **bit
strings**. Print's objects are not: a pair is a planner `p : ℛ → Π` with a
reward `R ∈ [-1, 1]^{𝒮×𝒜}`, a policy is `π : 𝒮 → 𝒜` (§3), and `K_L` is *"the
shortest algorithm in `L` that generates a particular object"* (§5.1.2). This
module says which strings describe which of print's objects, takes `K` of an
object to be the least `plainK` of a string describing it (`⊤` when none does,
as print's `K` is infinite on an object no algorithm generates), and transfers
the bit-string bound to the objects.

## The description scheme

Every string names a program through its run-length slot, `pairProgram`, which
reaches every program.

* **Policies** (`CodesPolicy b π`): `b`'s program computes `π`, state by state
  through `Encodable`. A discrete state space is a countable one, so no
  finiteness of `𝒮` is assumed.
* **Rewards** (`CodesReward r R`): `r`'s program computes `R` to any precision:
  on `(s, a, n)` it returns a rational within `2⁻ⁿ` of `R s a`. Every computable
  reward has a code, irrational values included.
* **Pairs** (`Describes y x`): `x`'s reward slot codes `y`'s reward, and `x`'s
  program is `y`'s planner on codes: run on any code of any reward `R'`, it
  returns a code of the policy `p R'`.

The scheme is the Atlas's choice; print leaves *"an algorithm generating the
object"* open. It is not silent on what it excludes: a planner that no program
computes on reward codes has no description, and its pairs get `⊤`. **Print's
greedy planner is one** (`greedyPlanner`, and its negation for the anti-rational
pair): an argmax over computable reals given by approximation programs is not
computable, so `(p_g, R_π̇)` and `(−p_g, −R_π̇)` have `K = ⊤` here, and the bound
below holds at them only because its right side is `⊤`. It has content at pairs
whose planner is computable on reward codes, such as the indifferent pair
`(p_π̇, R)`. Print's second §5.1 claim at the greedy pairs is not stated under
this scheme; it is stated with exact rational reward codes, and with a greedy
planner whose tie order is fixed, in `AISafetyAtlas.Preference.degenerate_near_minimal_exact`.

## What is proved

* `plainKPolicy_le_plainKPair_of_compatible` — print's claim (1) of §5.1: one
  constant, fixed before the pair and the policy, bounds `K(π̇)` by `K(p, R)` for
  every pair compatible with `π̇` (`ReasonableLanguage.Compatible`, `p(R) = π̇`).
  It is `behaviour_le_of_evaluatesTo` transported along the description scheme.
* `describes_degeneratePair` — the source's degenerate pair `(p_π̇, R)`
  (`indifferentPlanner π̇`) is described by the string `degeneratePair r b` of
  `AISafetyAtlas.Preference.Complexity` whenever `b` codes `π̇` and `r` codes `R`;
  so the class of described pairs is inhabited, and the docstring of
  `degeneratePair` ("this is `(p_π̇, R)`") has a theorem behind it.
-/

namespace AISafetyAtlas.Preference

open Kolmogorov
open Nat.Partrec (Code)

variable {S A : Type*} [Encodable S] [Encodable A]

/-- **A string codes a policy** when the program it names computes the policy:
on (the code of) every state it halts with (the code of) the policy's action. -/
@[expose] public def CodesPolicy (b : BitString) (π : Policy S A) : Prop :=
  ∀ s, Encodable.encode (π s) ∈ (pairProgram b).eval (Encodable.encode s)

/-- **A string codes a reward** when the program it names computes the reward to
any precision: on `(s, a, n)` it halts with a rational within `2⁻ⁿ` of `R s a`. -/
@[expose] public def CodesReward (r : BitString) (R : RewardFn S A) : Prop :=
  ∀ s a (n : ℕ), ∃ q : ℚ, Encodable.encode q ∈ (pairProgram r).eval (Encodable.encode (s, a, n)) ∧
    |R s a - q| ≤ (2⁻¹ : ℝ) ^ n

/-- Run a program on a string and read the result back as a string: the
operation `evalPair` performs on a pair's two slots. -/
@[expose] public noncomputable def runOn (c : Code) (r : BitString) : Part BitString :=
  (c.eval (Encodable.encode r)).bind fun n => (Encodable.decode (α := BitString) n : Part BitString)

/-- `evalPair` runs the pair's program on its reward slot. -/
public theorem evalPair_eq_runOn (x : BitString) :
    evalPair x = runOn (pairProgram x) (pairReward x) := rfl

/-- **A string describes a planner/reward pair**: its reward slot codes the
reward, and its program, run on any code of any reward `R'`, returns a code of
the policy the planner assigns to `R'`. -/
@[expose] public def Describes (y : Pair S A) (x : BitString) : Prop :=
  CodesReward (pairReward x) y.2 ∧
    ∀ (r : BitString) (R' : RewardFn S A), CodesReward r R' →
      ∃ b ∈ runOn (pairProgram x) r, CodesPolicy b (y.1 R')

variable (S A) in
/-- **`K(π)`**: the least plain complexity of a string coding `π`; `⊤` when no
program computes `π`. -/
@[expose] public noncomputable def plainKPolicy (U : Map) (π : Policy S A) : ENat :=
  sInf (plainK U '' {b | CodesPolicy b π})

variable (S A) in
/-- **`K(p, R)`**: the least plain complexity of a string describing the pair;
`⊤` when none does. -/
@[expose] public noncomputable def plainKPair (U : Map) (y : Pair S A) : ENat :=
  sInf (plainK U '' {x | Describes y x})

/-- A coding string bounds `K(π)`. -/
public theorem plainKPolicy_le_of_codesPolicy (U : Map) {π : Policy S A} {b : BitString}
    (hb : CodesPolicy b π) : plainKPolicy S A U π ≤ plainK U b :=
  sInf_le ⟨b, hb, rfl⟩

/-- A describing string bounds `K(p, R)`. -/
public theorem plainKPair_le_of_describes (U : Map) {y : Pair S A} {x : BitString}
    (hx : Describes y x) : plainKPair S A U y ≤ plainK U x :=
  sInf_le ⟨x, hx, rfl⟩

/-- **A description of a compatible pair evaluates to a code of the policy.** -/
public theorem exists_evaluatesTo_of_describes {y : Pair S A} {π : Policy S A}
    (h : ReasonableLanguage.Compatible y π) {x : BitString} (hx : Describes y x) :
    ∃ b, EvaluatesTo x b ∧ CodesPolicy b π := by
  obtain ⟨b, hb, hcode⟩ := hx.2 (pairReward x) y.2 hx.1
  refine ⟨b, hb, ?_⟩
  have h' : y.1 y.2 = π := h
  rwa [h'] at hcode

/--
**Print's §5.1 claim (1), at print's objects** (Armstrong and Mindermann, §5.1,
`am-lower-bound`, PDF p. 5: *"the complexity of `π̇` is close to a lower bound on
any pair compatible with it ... the map `(p, R) ↦ p(R) = π̇` will be a simple
one"*). For an optimal conditional decompressor `U` there is one constant `c`,
fixed before the pair and the policy, such that for every planner/reward pair
`y = (p, R)` and every policy `π̇` with `p(R) = π̇`, `K(π̇) ≤ K(p, R) + c`, with
`K` the least plain complexity of a describing string (`⊤` if none). Any state
type with an encoding (print's discrete `𝒮`), any encodable action type.
-/
public theorem plainKPolicy_le_plainKPair_of_compatible (U : Map)
    (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (y : Pair S A) (π : Policy S A), ReasonableLanguage.Compatible y π →
      plainKPolicy S A U π ≤ plainKPair S A U y + (c : ENat) := by
  obtain ⟨c, hc⟩ := behaviour_le_of_evaluatesTo U hU
  refine ⟨c, fun y π h => ?_⟩
  rcases (plainK U '' {x | Describes y x}).eq_empty_or_nonempty with hE | hE
  · rw [plainKPair, hE, sInf_empty, top_add]
    exact le_top
  · obtain ⟨x, hx, hxK⟩ := csInf_mem hE
    obtain ⟨b, hev, hcode⟩ := exists_evaluatesTo_of_describes h hx
    rw [plainKPair, ← hxK]
    exact (plainKPolicy_le_of_codesPolicy U hcode).trans (hc x b hev)

/--
**The source's degenerate pair is described** (§5.1: *"`(p_π̇, 0)`"*, here at
any reward `R`). If `b` codes `π̇` and `r` codes `R`, the string
`degeneratePair r b` (the constant program returning `b`, then `r`) describes
`(p_π̇, R)`, with `p_π̇ = indifferentPlanner π̇`.
-/
public theorem describes_degeneratePair {π : Policy S A} {b : BitString}
    (hb : CodesPolicy b π) {R : RewardFn S A} {r : BitString} (hr : CodesReward r R) :
    Describes (indifferentPlanner π, R) (degeneratePair r b) := by
  refine ⟨by rwa [degeneratePair, pairReward_pairString], fun r' R' _ => ⟨b, ?_, hb⟩⟩
  rw [runOn, degeneratePair, pairProgram_pairString, Denumerable.ofNat_encode, Code.eval_const]
  simp [Encodable.encodek]

end AISafetyAtlas.Preference
