module

public import AISafetyAtlas.Decision.Occupancy

/-!
# Hackability: when two reward functions disagree about which policy is better

Skalse, Howe, Krasheninnikov and Krueger, *Defining and Characterizing Reward
Hacking*, NeurIPS 2022, sha256
`634ffa7ccb0225296482ef2961a38ba175bd8c1b97b998556a6bcfa7ad560210`, §4.2, read
from rendered page 5.

**This is a relation between two reward functions**, and it is the first object
of that kind in the atlas. The other Goodhart modules — `Regressional`,
`Extremal`, `Overoptimization` — all ask what happens when you *optimize* a
proxy. This asks something else: given two reward functions, do the orderings
they induce on a set of policies ever disagree?

> **Definition 1.** A pair of reward functions `ℛ₁, ℛ₂` are **hackable** relative
> to policy set `Π` and an environment `(S, A, T, I, _, γ)` if there exist
> `π, π′ ∈ Π` such that `J₁(π) < J₁(π′) & J₂(π) > J₂(π′)`, else they are
> **unhackable**.

> **Definition 2.** `ℛ₂` is a **simplification** of `ℛ₁` relative to policy set
> `Π` if for all `π, π′ ∈ Π`, `J₁(π) < J₁(π′) ⟹ J₂(π) ≤ J₂(π′)` and
> `J₁(π) = J₁(π′) ⟹ J₂(π) = J₂(π′)`, and there exist `π, π′ ∈ Π` such that
> `J₂(π) = J₂(π′)` but `J₁(π) ≠ J₁(π′)`. Moreover, if `ℛ₂` is trivial then we
> say that this is a **trivial simplification**.

## Stated on the induced value, which is wider and is print's content

Print's relation is between reward functions, and print says in the same breath
that it is *"mediated by the ordering each induces"* on the policy set: nothing
in either definition mentions a reward except through its `J`. So the definitions
here take the two value functions, and `AISafetyAtlas.Decision.J` supplies them
from a reward, an environment, an initial distribution and a discount —
`HackableRewards` and the rest of the `…Rewards` family are print's statements at
print's arguments.

The widening is free and it is not idle: a value function that comes from no
reward at all — an ordering elicited from a human, say — is a legitimate
argument, and every theorem below applies to it.

## Print's own side conditions, §4.2

All four are proved here, in the order print states them.

* Unhackability is **symmetric**, *"which can be seen by swapping `π` and `π′`"*
  — `Unhackable.symm`.
* Equivalent reward functions are unhackable, and so is any pair one of which is
  trivial — `unhackable_of_equivalent`, `unhackable_of_trivial_left`.
* Unhackability is **not transitive**, *"since the constant reward function is
  unhackable with respect to any other reward function, so if it were transitive,
  any pair of policies would be unhackable"* — `unhackable_not_transitive`.
* Footnote 4: if `ℛ₁ ⊴ ℛ₂ ⊵ ℛ₃` then `ℛ₁, ℛ₃` are unhackable —
  `unhackable_of_simplifies_common`, at print's own two-step argument.
* Footnote 5: the other arrangement `ℛ₁ ⊵ ℛ₂ ⊴ ℛ₃` gives nothing, *"consider the
  case where `ℛ₂` is trivial"* — `simplifies_of_trivial` supplies that case and
  `unhackable_not_transitive` is the failure it produces.

**One place print is loose, and it is in footnote 5.** Print says a trivial `ℛ₂`
is a simplification of *any* `ℛ₁`. Definition 2's own non-degeneracy clause asks
for two policies the simplification identifies and `ℛ₁` separates, so `ℛ₁` must
be non-trivial for the claim to hold; at a trivial `ℛ₁` there is no such pair and
`ℛ₂` is not a simplification of it. `simplifies_of_trivial` carries that
hypothesis and `AISafetyAtlas.Examples.Goodhart.not_simplifies_of_trivial_both`
shows it cannot be dropped.

## What is not here

Lemma 1 and Theorems 1, 2 and 3 — the geometry. Section 26 of
`docs/provenance/source-coverage-audit.md` costs each.
-/

namespace AISafetyAtlas.Goodhart

universe u v w

variable {Pol : Type u}

/-! ## Definition 1 -/

/--
**Print's Definition 1.** Two value functions are *hackable* on a policy set when
some pair of policies in it is ranked one way by the first and the other way by
the second.
-/
@[expose] public def Hackable (Pi : Set Pol) (J₁ J₂ : Pol → ℝ) : Prop :=
  ∃ π ∈ Pi, ∃ π' ∈ Pi, J₁ π < J₁ π' ∧ J₂ π' < J₂ π

/-- **Unhackable** is print's negation: no such pair exists. -/
@[expose] public def Unhackable (Pi : Set Pol) (J₁ J₂ : Pol → ℝ) : Prop :=
  ¬ Hackable Pi J₁ J₂

/-- **Print's *equivalent*:** the two induce the same strict ordering of the
policy set. -/
@[expose] public def Equivalent (Pi : Set Pol) (J₁ J₂ : Pol → ℝ) : Prop :=
  ∀ π ∈ Pi, ∀ π' ∈ Pi, (J₁ π < J₁ π' ↔ J₂ π < J₂ π')

/-- **Print's *trivial*:** every policy in the set is worth the same. -/
@[expose] public def Trivial (Pi : Set Pol) (J : Pol → ℝ) : Prop :=
  ∀ π ∈ Pi, ∀ π' ∈ Pi, J π = J π'

/-! ## Definition 2 -/

/--
**Print's Definition 2**: `J₂` *simplifies* `J₁`. Every strict preference of
`J₁` is at worst weakened by `J₂` and every indifference of `J₁` is kept, and at
least one distinction is genuinely lost.

The third clause is print's own non-degeneracy requirement, and without it every
trivial value function would simplify everything.
-/
@[expose] public def Simplifies (Pi : Set Pol) (J₂ J₁ : Pol → ℝ) : Prop :=
  (∀ π ∈ Pi, ∀ π' ∈ Pi, J₁ π < J₁ π' → J₂ π ≤ J₂ π') ∧
    (∀ π ∈ Pi, ∀ π' ∈ Pi, J₁ π = J₁ π' → J₂ π = J₂ π') ∧
    (∃ π ∈ Pi, ∃ π' ∈ Pi, J₂ π = J₂ π' ∧ J₁ π ≠ J₁ π')

/-- **Print's *trivial simplification*.** -/
@[expose] public def TrivialSimplification (Pi : Set Pol) (J₂ J₁ : Pol → ℝ) : Prop :=
  Simplifies Pi J₂ J₁ ∧ Trivial Pi J₂

/-! ## Print's side conditions -/

/-- **Unhackability is symmetric**, by print's own argument: swap the two
policies. -/
public theorem Unhackable.symm {Pi : Set Pol} {J₁ J₂ : Pol → ℝ}
    (h : Unhackable Pi J₁ J₂) : Unhackable Pi J₂ J₁ := by
  rintro ⟨π, hπ, π', hπ', h₂, h₁⟩
  exact h ⟨π', hπ', π, hπ, h₁, h₂⟩

/-- **Equivalent value functions are unhackable.** -/
public theorem unhackable_of_equivalent {Pi : Set Pol} {J₁ J₂ : Pol → ℝ}
    (h : Equivalent Pi J₁ J₂) : Unhackable Pi J₁ J₂ := by
  rintro ⟨π, hπ, π', hπ', h₁, h₂⟩
  exact absurd ((h π hπ π' hπ').mp h₁) (not_lt_of_gt h₂)

/-- **A trivial value function is unhackable against everything.** -/
public theorem unhackable_of_trivial_left {Pi : Set Pol} {J₁ J₂ : Pol → ℝ}
    (h : Trivial Pi J₁) : Unhackable Pi J₁ J₂ := by
  rintro ⟨π, hπ, π', hπ', h₁, -⟩
  exact absurd (h π hπ π' hπ') (ne_of_lt h₁)

/-- And on the other side, by symmetry. -/
public theorem unhackable_of_trivial_right {Pi : Set Pol} {J₁ J₂ : Pol → ℝ}
    (h : Trivial Pi J₂) : Unhackable Pi J₁ J₂ :=
  Unhackable.symm (unhackable_of_trivial_left h)

/--
**Unhackability is not transitive**, and print's reason is the whole proof: put
a trivial value function in the middle and it is unhackable against both sides,
whatever those sides do to each other.

Stated with the two ends' disagreement as a hypothesis rather than at a fixed
model, so that it says what fails rather than exhibiting one failure;
`AISafetyAtlas.Examples.Goodhart.hackable_bit` inhabits it.
-/
public theorem unhackable_not_transitive {Pi : Set Pol} {J₁ J₂ J₃ : Pol → ℝ}
    (h₂ : Trivial Pi J₂) (h₁₃ : Hackable Pi J₁ J₃) :
    Unhackable Pi J₁ J₂ ∧ Unhackable Pi J₂ J₃ ∧ ¬ Unhackable Pi J₁ J₃ :=
  ⟨unhackable_of_trivial_right h₂, unhackable_of_trivial_left h₂, fun h => h h₁₃⟩

/-! ## The two footnotes on the refinement relation -/

/--
**Print's footnote 4.** If `J₁` and `J₃` both simplify a common `J₂`, they are
unhackable against each other.

Print's argument, in print's order: a strict preference of `J₃` forces one of
`J₂`, because a reversal would be weakened and an indifference would be kept;
and a strict preference of `J₂` then forces a weak one of `J₁`.
-/
public theorem unhackable_of_simplifies_common {Pi : Set Pol} {J₁ J₂ J₃ : Pol → ℝ}
    (h₁ : Simplifies Pi J₁ J₂) (h₃ : Simplifies Pi J₃ J₂) :
    Unhackable Pi J₁ J₃ := by
  rintro ⟨π, hπ, π', hπ', hlt₁, hlt₃⟩
  -- `J₃ π' < J₃ π` forces `J₂ π' < J₂ π`.
  have hlt₂ : J₂ π' < J₂ π := by
    rcases lt_trichotomy (J₂ π') (J₂ π) with h | h | h
    · exact h
    · exact absurd (h₃.2.1 π' hπ' π hπ h) (ne_of_lt hlt₃)
    · exact absurd (h₃.1 π hπ π' hπ' h) (not_le_of_gt hlt₃)
  -- and `J₂ π' < J₂ π` forces `J₁ π' ≤ J₁ π`, which contradicts `J₁ π < J₁ π'`.
  exact absurd (h₁.1 π' hπ' π hπ hlt₂) (not_le_of_gt hlt₁)

/--
**Print's footnote 5**, with the hypothesis print leaves out. A trivial value
function simplifies any value function that is *not* trivial: every preference
is weakened to indifference, and the two policies the base separates are the
non-degeneracy witness.

Print says "for any `ℛ₁`", but Definition 2's third clause fails outright at a
trivial base, so non-triviality is needed and is not a strengthening of the
statement print uses the claim for.
-/
public theorem simplifies_of_trivial {Pi : Set Pol} {J₁ J₂ : Pol → ℝ}
    (h₂ : Trivial Pi J₂) (h₁ : ∃ π ∈ Pi, ∃ π' ∈ Pi, J₁ π ≠ J₁ π') :
    Simplifies Pi J₂ J₁ := by
  obtain ⟨π, hπ, π', hπ', hne⟩ := h₁
  exact ⟨fun a ha b hb _ => le_of_eq (h₂ a ha b hb),
    fun a ha b hb _ => h₂ a ha b hb,
    ⟨π, hπ, π', hπ', h₂ π hπ π' hπ', hne⟩⟩

/-- **And it fails at a trivial base**, which is why the hypothesis above is
there: Definition 2's non-degeneracy clause asks for a distinction to lose, and
a trivial value function has none. -/
public theorem not_simplifies_of_trivial_base {Pi : Set Pol} {J₁ J₂ : Pol → ℝ}
    (h₁ : Trivial Pi J₁) : ¬ Simplifies Pi J₂ J₁ := by
  rintro ⟨-, -, π, hπ, π', hπ', -, hne⟩
  exact hne (h₁ π hπ π' hπ')

/-! ## Print's statements at print's arguments

Definition 1 and Definition 2 relate two **reward functions** in an `MDP \ ℛ`.
These are those, with `AISafetyAtlas.Decision.J` supplying the ordering each
reward induces.
-/

variable {State : Type v} {Action : Type w}

/-- **Definition 1 between two reward functions.** -/
@[expose] public def HackableRewards [Fintype State] [Fintype Action]
    (M : Decision.MDP State Action) (I : PMF State) (γ : NNReal)
    (Pi : Set (State → PMF Action)) (R₁ R₂ : State → Action → ℝ) : Prop :=
  Hackable Pi (Decision.J M I γ R₁) (Decision.J M I γ R₂)

/-- **Unhackable between two reward functions.** -/
@[expose] public def UnhackableRewards [Fintype State] [Fintype Action]
    (M : Decision.MDP State Action) (I : PMF State) (γ : NNReal)
    (Pi : Set (State → PMF Action)) (R₁ R₂ : State → Action → ℝ) : Prop :=
  Unhackable Pi (Decision.J M I γ R₁) (Decision.J M I γ R₂)

/-- **Definition 2 between two reward functions**: `R₂` simplifies `R₁`. -/
@[expose] public def SimplifiesRewards [Fintype State] [Fintype Action]
    (M : Decision.MDP State Action) (I : PMF State) (γ : NNReal)
    (Pi : Set (State → PMF Action)) (R₂ R₁ : State → Action → ℝ) : Prop :=
  Simplifies Pi (Decision.J M I γ R₂) (Decision.J M I γ R₁)

/--
**A constant reward is trivial on every policy set**, which is the fact print's
non-transitivity argument runs on: it makes the middle term of the chain
available in every environment rather than only in a contrived one.

The discounted horizon is spent somewhere whatever the policy does, so a reward
that pays the same everywhere pays every policy the same.
-/
public theorem trivial_of_const [Fintype State] [Fintype Action]
    (M : Decision.MDP State Action) (I : PMF State) {γ : NNReal} (hγ : γ < 1)
    (Pi : Set (State → PMF Action)) (c : ℝ) :
    Trivial Pi (Decision.J M I γ fun _ _ => c) := fun π _ π' _ => by
  rw [Decision.J_const_eq M I hγ c π, Decision.J_const_eq M I hγ c π']

end AISafetyAtlas.Goodhart
