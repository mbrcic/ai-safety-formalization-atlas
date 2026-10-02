module

import AISafetyAtlas.Wireheading.GoalPreservationRun

/-!
# A model that really self-modifies, and in which the new hypotheses bite

`Wireheading.GoalPreservationRun` proves equation (13) of Everitt, Filan,
Daswani and Hutter's Theorem 16 under `bellman` and `initial_optimal` in place
of `GoalPreservation`'s naming surjectivity. Both replacements are printed
hypotheses, so the theorem is only worth as much as their satisfiability.

`alternatingModel` inhabits them, and it is built so that each of the three
things a reader would otherwise have to check by hand is visible:

* **The agent genuinely changes policy.** `act` maps the initial name to a
  *different* name, so `run` alternates and `π_t ≠ π₁` at every odd `t`.
  Equation (13) is therefore an equality between the values of two *different*
  action pairs, not a reflexivity.
* **`contValue` is not constant**, so `contValue_le_initial` — the field
  `GoalPreservationSource.Model` assumes and this module derives — is a strict
  inequality somewhere rather than an equality everywhere.
* **`initial_optimal` is not free.** A world action strictly worse than the one
  `π₁` takes exists, and the model rules it out by making `π₁` prefer the good
  one.

## The model

Two world actions, `false` (pays `1/2` per step) and `true` (pays `0`). The
history records the last world action. Policy names are natural numbers:
`0` and `1` are the two "good" names, each installing the other; every name from
`2` on plays `true` forever and installs itself. Discount `1/2`, two percepts
with uniform full support, and the percept is discarded by `extend` — which is
legitimate, since print quantifies over percept sequences and asserts nothing
about the history depending on them.
-/

namespace AISafetyAtlas.Examples.Wireheading.GoalPreservationRun

open AISafetyAtlas.Wireheading.GoalPreservationRun

/-- The alternating self-modification model. -/
noncomputable def alternatingModel : Model Bool Bool ℕ Bool where
  act := fun p _ => if p = 0 then (false, 1) else if p = 1 then (false, 0)
    else (true, p)
  extend := fun _ w _ => w
  utility := fun h => if h then 0 else 1 / 2
  discount := 1 / 2
  discount_pos := by norm_num
  prob := fun _ _ _ => 1 / 2
  prob_sum_one := by intro h a; simp
  prob_pos := by intro h a e; norm_num
  contValue := fun p _ => if p ≤ 1 then 1 else 0
  initial := 0
  bellman := by
    intro p h
    match p with
    | 0 => simp; norm_num
    | 1 => simp; norm_num
    | (n + 2) => simp
  initial_optimal := by
    rintro h ⟨w, q⟩
    cases w <;> simp <;> split_ifs <;> norm_num

/-! ## The agent does not stay put -/

/-- After one step the policy in force is `1`, not the initial `0`. -/
example (percepts : ℕ → Bool) (start : Bool) :
    (alternatingModel.run percepts start 1).1 = 1 := by
  simp [Model.run, alternatingModel]

/-- After two steps it is back to `0`. The trajectory is a genuine
self-modification cycle, not a fixed point. -/
example (percepts : ℕ → Bool) (start : Bool) :
    (alternatingModel.run percepts start 2).1 = 0 := by
  simp [Model.run, alternatingModel]

/-! ## The derived domination is strict somewhere

`contValue_le_initial` is what `GoalPreservationSource.Model` takes as a field.
Here it is derived — and here is a name it separates.
-/

example (h : Bool) :
    alternatingModel.contValue 2 h < alternatingModel.contValue
      alternatingModel.initial h := by
  simp [alternatingModel]

example (p : ℕ) (h : Bool) :
    alternatingModel.contValue p h ≤ alternatingModel.contValue
      alternatingModel.initial h :=
  alternatingModel.contValue_le_initial p h

/-! ## Equation (13), on this model, at every step of every percept sequence -/

example (percepts : ℕ → Bool) (start : Bool) (n : ℕ) :
    alternatingModel.qValue (alternatingModel.run percepts start n).2
        (alternatingModel.act (alternatingModel.run percepts start n).1
          (alternatingModel.run percepts start n).2) =
      alternatingModel.qValue (alternatingModel.run percepts start n).2
        (alternatingModel.act alternatingModel.initial
          (alternatingModel.run percepts start n).2) :=
  alternatingModel.equation_thirteen percepts start n

/--
At step `1` the two sides of equation (13) are the values of **different**
action pairs — `(false, 0)` for the current policy and `(false, 1)` for the
initial one — so the equality has content.
-/
example (percepts : ℕ → Bool) (start : Bool) :
    alternatingModel.act (alternatingModel.run percepts start 1).1
        (alternatingModel.run percepts start 1).2 ≠
      alternatingModel.act alternatingModel.initial
        (alternatingModel.run percepts start 1).2 := by
  simp [Model.run, alternatingModel]

/-- Optimality really does propagate along the trajectory. -/
example (percepts : ℕ → Bool) (start : Bool) (n : ℕ) :
    alternatingModel.OptimalAt (alternatingModel.run percepts start n).1
      (alternatingModel.run percepts start n).2 :=
  alternatingModel.run_optimal percepts start n

/-!
## Print's `𝒫 ≠ Π`, exhibited

Definition 3 sets `Π` to the full space of maps from histories to actions and
`ι : 𝒫 → Π` to the naming map, then observes that *"some policies will
necessarily lack names"*.  No result in this atlas assumes `ι` onto; this
witness shows that is not a vacuous restraint, because in this model it is not.

`alternatingModel.act` ignores the history, so every named policy is constant,
and the policy that returns its own history is unnamed.
-/

/-- The naming map of a concrete model that is **not** surjective. -/
example : ¬ Function.Surjective alternatingModel.name := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (fun h => (h, 0))
  have h₁ : alternatingModel.name p false = (false, 0) := by rw [hp]
  have h₂ : alternatingModel.name p true = (true, 0) := by rw [hp]
  have hconst : alternatingModel.name p false = alternatingModel.name p true := rfl
  rw [h₁, h₂] at hconst
  simp at hconst

/-! ## What is not shown

That a model satisfying `initial_optimal` exists whenever print's setting does.
Print gets that from its Appendix A Theorems 20 and 21, which the atlas does
not carry; this example exhibits one model, not the general construction.
-/

/-! ## Three leaves, named rather than left as `example`s

Each of the three facts below was already exercised somewhere above as an
anonymous `example`, which demonstrates but does not ground. Naming them is
the whole fix. -/

/-- `ι(p)` is `act p`, definitionally, at the witness. -/
theorem alternatingModel_name_eq_act (p : ℕ) :
    alternatingModel.name p = alternatingModel.act p :=
  Model.name_eq_act alternatingModel p

/-- Optimality propagates along the whole trajectory, named. -/
theorem alternatingModel_run_optimal (percepts : ℕ → Bool) (start : Bool) (n : ℕ) :
    alternatingModel.OptimalAt (alternatingModel.run percepts start n).1
      (alternatingModel.run percepts start n).2 :=
  Model.run_optimal alternatingModel percepts start n

/-- The continuation value along the run equals the continuation value at the
initial policy, named. -/
theorem alternatingModel_run_contValue_eq_initial (percepts : ℕ → Bool) (start : Bool) (n : ℕ) :
    alternatingModel.contValue (alternatingModel.run percepts start n).1
        (alternatingModel.run percepts start n).2 =
      alternatingModel.contValue alternatingModel.initial
        (alternatingModel.run percepts start n).2 :=
  Model.run_contValue_eq_initial alternatingModel percepts start n

end AISafetyAtlas.Examples.Wireheading.GoalPreservationRun
