module

public import AISafetyAtlas.Goodhart.Hackability
public import AISafetyAtlas.Examples.Decision.Occupancy

/-!
# Two rewards that disagree, on one state and two actions

Every definition and every side condition in `AISafetyAtlas.Goodhart.Hackability`
is inhabited here. The environment is
`AISafetyAtlas.Examples.Decision.oneState`: one state, two actions, discount one
half, so a policy is a point of the interval and `J` reads off the reward it
expects, doubled.

**The hackable pair is the smallest one there is.** `rewardFalse` pays for taking
`false` and `rewardTrue` pays for taking `true`. Switching from `pickTrue` to
`pickFalse` raises the first from `0` to `2` and lowers the second from `2` to
`0` — print's Definition 1 with nothing left over.

**The trivial reward is print's own non-transitivity argument.** A constant
reward pays every policy the same, so it is unhackable against both ends of any
chain, whatever those ends do to each other. `notTransitive` is that failure at
the pair above.

## Footnote 4 is witnessed abstractly, and it has to be

`unhackable_of_simplifies_common` asks for two value functions that both simplify
a common third. On this environment `J` is **affine** in the probability of
taking `true`, so on any three policies the three values are in arithmetic
progression — and an affine function that identifies two of three equally spaced
points is constant. So no non-trivial simplification of a non-trivial reward
exists here at all, and the witness runs on the abstract form of the definitions
instead, at three policies and values read off directly.

That is not a defect of the model. It is a small instance of what print's
Theorem 3 measures, and it is the reason the definitions in the library are
stated on the induced value rather than on the reward.
-/

namespace AISafetyAtlas.Examples.Goodhart

open AISafetyAtlas.Goodhart
open AISafetyAtlas.Decision
open AISafetyAtlas.Examples.Decision

/-! ## The two rewards -/

/-- Pays one for taking `false`, nothing for taking `true`. -/
@[expose] public def rewardFalse : Unit → Bool → ℝ := fun _ a => if a then 0 else 1

/-- The other way round. -/
@[expose] public def rewardTrue : Unit → Bool → ℝ := fun _ a => if a then 1 else 0

/-- **The value of a deterministic policy is twice what the reward pays it.** -/
public theorem J_pure (R : Unit → Bool → ℝ) (b : Bool) :
    J oneState startHere half R (fun _ => PMF.pure b) = 2 * R () b := by
  rw [J_unit oneState _ startHere half_lt_one R, horizon_half]
  cases b <;> simp [PMF.pure_apply]

public theorem J_rewardFalse_pickFalse :
    J oneState startHere half rewardFalse pickFalse = 2 := by
  show J oneState startHere half rewardFalse (fun _ => PMF.pure false) = 2
  rw [J_pure rewardFalse false]
  norm_num [rewardFalse]

public theorem J_rewardFalse_pickTrue :
    J oneState startHere half rewardFalse pickTrue = 0 := by
  show J oneState startHere half rewardFalse (fun _ => PMF.pure true) = 0
  rw [J_pure rewardFalse true]
  norm_num [rewardFalse]

public theorem J_rewardTrue_pickFalse :
    J oneState startHere half rewardTrue pickFalse = 0 := by
  show J oneState startHere half rewardTrue (fun _ => PMF.pure false) = 0
  rw [J_pure rewardTrue false]
  norm_num [rewardTrue]

public theorem J_rewardTrue_pickTrue :
    J oneState startHere half rewardTrue pickTrue = 2 := by
  show J oneState startHere half rewardTrue (fun _ => PMF.pure true) = 2
  rw [J_pure rewardTrue true]
  norm_num [rewardTrue]

/-! ## Definition 1, inhabited -/

/--
**The two rewards are hackable.** Moving from `pickTrue` to `pickFalse` is an
improvement by the first and a loss by the second, which is exactly print's
Definition 1.
-/
public theorem hackable_rewards :
    HackableRewards oneState startHere half (Set.univ : Set (Unit → PMF Bool))
      rewardFalse rewardTrue := by
  refine ⟨pickTrue, trivial, pickFalse, trivial, ?_, ?_⟩
  · rw [J_rewardFalse_pickTrue, J_rewardFalse_pickFalse]
    norm_num
  · rw [J_rewardTrue_pickFalse, J_rewardTrue_pickTrue]
    norm_num

/-- The same fact under the abstract definition, which is what the side
conditions consume. -/
public theorem hackable_bit :
    Hackable (Set.univ : Set (Unit → PMF Bool))
      (J oneState startHere half rewardFalse) (J oneState startHere half rewardTrue) :=
  hackable_rewards

/-! ## Trivial rewards, and print's non-transitivity argument -/

/-- A reward that pays one whatever happens. -/
@[expose] public def rewardConst : Unit → Bool → ℝ := fun _ _ => 1

/-- **It is trivial on every policy set**, by `trivial_of_const`. -/
public theorem trivial_rewardConst (Pi : Set (Unit → PMF Bool)) :
    Trivial Pi (J oneState startHere half rewardConst) :=
  trivial_of_const oneState startHere half_lt_one Pi 1

/-- Unhackable against the first reward, because it is trivial. -/
public theorem unhackable_const_false :
    Unhackable (Set.univ : Set (Unit → PMF Bool))
      (J oneState startHere half rewardConst) (J oneState startHere half rewardFalse) :=
  unhackable_of_trivial_left (trivial_rewardConst _)

/-- And against the second, on the other side. -/
public theorem unhackable_true_const :
    Unhackable (Set.univ : Set (Unit → PMF Bool))
      (J oneState startHere half rewardTrue) (J oneState startHere half rewardConst) :=
  unhackable_of_trivial_right (trivial_rewardConst _)

/-- Unhackability is symmetric, at the pair above. -/
public theorem unhackable_false_const :
    Unhackable (Set.univ : Set (Unit → PMF Bool))
      (J oneState startHere half rewardFalse) (J oneState startHere half rewardConst) :=
  Unhackable.symm unhackable_const_false

/--
**Print's non-transitivity, inhabited.** The constant reward is unhackable
against both of a hackable pair, so unhackability does not compose.
-/
public theorem notTransitive :
    Unhackable (Set.univ : Set (Unit → PMF Bool))
        (J oneState startHere half rewardFalse) (J oneState startHere half rewardConst)
      ∧ Unhackable (Set.univ : Set (Unit → PMF Bool))
        (J oneState startHere half rewardConst) (J oneState startHere half rewardTrue)
      ∧ ¬ Unhackable (Set.univ : Set (Unit → PMF Bool))
        (J oneState startHere half rewardFalse) (J oneState startHere half rewardTrue) :=
  unhackable_not_transitive (trivial_rewardConst _) hackable_bit

/-! ## Equivalence -/

/-- **Doubling a reward does not change the ordering it induces**, by
homogeneity of `J`. -/
public theorem equivalent_double :
    Equivalent (Set.univ : Set (Unit → PMF Bool))
      (J oneState startHere half rewardFalse)
      (J oneState startHere half fun s a => 2 * rewardFalse s a) := by
  intro π _ π' _
  rw [J_smul_here 2 rewardFalse π, J_smul_here 2 rewardFalse π']
  constructor
  · intro h; linarith
  · intro h; linarith

/-- And so the two are unhackable, by `unhackable_of_equivalent`. -/
public theorem unhackable_double :
    Unhackable (Set.univ : Set (Unit → PMF Bool))
      (J oneState startHere half rewardFalse)
      (J oneState startHere half fun s a => 2 * rewardFalse s a) :=
  unhackable_of_equivalent equivalent_double

/-! ## Definition 2, and print's two footnotes -/

/-- **The constant reward is a simplification of a reward that separates two
policies** — print's footnote 5, with the non-triviality hypothesis print omits
supplied by the hackable pair. -/
public theorem simplifies_const :
    SimplifiesRewards oneState startHere half (Set.univ : Set (Unit → PMF Bool))
      rewardConst rewardFalse := by
  refine simplifies_of_trivial (trivial_rewardConst _) ⟨pickTrue, trivial, pickFalse, trivial, ?_⟩
  rw [J_rewardFalse_pickTrue, J_rewardFalse_pickFalse]
  norm_num

/-- And it is a **trivial** simplification, print's own name for it. -/
public theorem trivialSimplification_const :
    TrivialSimplification (Set.univ : Set (Unit → PMF Bool))
      (J oneState startHere half rewardConst) (J oneState startHere half rewardFalse) :=
  ⟨simplifies_const, trivial_rewardConst _⟩

/--
**Print's footnote 5 fails at a trivial base**, which is why
`simplifies_of_trivial` carries the hypothesis it does: nothing simplifies a
reward that already draws no distinctions.
-/
public theorem not_simplifies_of_trivial_both :
    ¬ Simplifies (Set.univ : Set (Unit → PMF Bool))
      (J oneState startHere half rewardTrue) (J oneState startHere half rewardConst) :=
  not_simplifies_of_trivial_base (trivial_rewardConst _)

/-! ## Footnote 4, at three policies and three orderings

The abstract form, for the reason the module docstring gives: `J` is affine on
this environment, so the identifications footnote 4 needs cannot come from a
reward here.
-/

/-- Three policies, kept abstract. -/
public abbrev Three : Type := Fin 3

/-- The value function the other two simplify: it separates all three. -/
@[expose] public def base3 : Three → ℝ := ![0, 1, 2]

/-- One simplification, which identifies the first two. -/
@[expose] public def coarseLow : Three → ℝ := ![0, 0, 1]

/-- Another, which identifies the last two. -/
@[expose] public def coarseHigh : Three → ℝ := ![0, 1, 1]

public theorem simplifies_coarseLow :
    Simplifies (Set.univ : Set Three) coarseLow base3 := by
  refine ⟨?_, ?_, ⟨0, trivial, 1, trivial, ?_, ?_⟩⟩
  · intro a _ b _ h
    fin_cases a <;> fin_cases b <;> simp_all [base3, coarseLow]
    linarith
  · intro a _ b _ h
    fin_cases a <;> fin_cases b <;> simp_all [base3, coarseLow]
  · simp [coarseLow]
  · simp [base3]

public theorem simplifies_coarseHigh :
    Simplifies (Set.univ : Set Three) coarseHigh base3 := by
  refine ⟨?_, ?_, ⟨1, trivial, 2, trivial, ?_, ?_⟩⟩
  · intro a _ b _ h
    fin_cases a <;> fin_cases b <;> simp_all [base3, coarseHigh] <;> linarith
  · intro a _ b _ h
    fin_cases a <;> fin_cases b <;> simp_all [base3, coarseHigh]
  · simp [coarseHigh]
  · simp [base3]

/-- **Print's footnote 4, inhabited**: two value functions that simplify a common
third are unhackable against each other, and here neither is trivial and the two
are not equal. -/
public theorem unhackable_coarse :
    Unhackable (Set.univ : Set Three) coarseLow coarseHigh :=
  unhackable_of_simplifies_common simplifies_coarseLow simplifies_coarseHigh

/-- The two simplifications are genuinely different, so footnote 4 is not being
inhabited by an equality in disguise. -/
public theorem coarse_ne : coarseLow ≠ coarseHigh := by
  intro h
  have := congrFun h 1
  simp [coarseLow, coarseHigh] at this

/-- Print's second embedding, at the model: the policy read off as its action
probabilities. -/
public theorem actionEmbed_pickFalse (a : Bool) :
    actionEmbed pickFalse () a = if a then 0 else 1 := by
  cases a <;> simp [actionEmbed, pickFalse, PMF.pure_apply]

/-- And the relationship between the two embeddings, at the model. -/
public theorem visitCount_factors (π : Unit → PMF Bool) (a : Bool) :
    visitCount oneState π startHere half () a
      = stateOcc oneState π startHere half () * actionEmbed π () a :=
  visitCount_eq_stateOcc_mul_actionEmbed oneState π startHere half () a

/-! ## The reward-level names -/

/-- `UnhackableRewards`, inhabited: the constant reward against either of the
other two. -/
public theorem unhackableRewards_const :
    UnhackableRewards oneState startHere half (Set.univ : Set (Unit → PMF Bool))
      rewardConst rewardFalse :=
  unhackable_const_false

end AISafetyAtlas.Examples.Goodhart
