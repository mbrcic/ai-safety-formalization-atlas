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


/-! ## Wave 3: histories that record the selected name

`NamedModel` admits a policy whose world action reads the name selected at the
previous step, which the name-erasing `Model` cannot express. `namedEcho` is one:
the world action is the last recorded name. Utility and values are zero, so the
modification-independence fields and the Bellman equation hold; the model shows
the carrier is inhabited by a name-reading policy, not that its values are
interesting. `alternatingModel.toNamed` is the embedding of a nontrivial `Model`.
-/

/-- The last selected policy name recorded in a history, `false` if none. -/
def lastName : List ((Bool × Bool) × Unit) → Bool := fun h ↦
  match h.getLast? with
  | none => false
  | some ((_, q), _) => q

/-- A name-recording model whose world action is the previously selected name. -/
noncomputable def namedEcho : NamedModel (List ((Bool × Bool) × Unit)) Bool Bool Unit where
  act := fun p h ↦ (lastName h, p)
  extend := fun h a e ↦ h ++ [(a, e)]
  utility := fun _ ↦ 0
  discount := 1 / 2
  discount_pos := by norm_num
  prob := fun _ _ _ ↦ 1
  prob_sum_one := by intro h a; simp
  prob_pos := by intro h a e; norm_num
  contValue := fun _ _ ↦ 0
  initial := false
  utility_modIndep := fun _ _ _ _ _ ↦ rfl
  initial_modIndep := fun _ _ _ _ _ ↦ rfl
  bellman := by intro p h; simp
  initial_optimal := by intro h a; simp

/-- The world action genuinely reads the recorded name. -/
theorem namedEcho_reads_name :
    (namedEcho.act false [((false, true), ())]).1 = true := rfl

/-- **Equation (13) with names in the history**, at the name-reading model. -/
theorem namedEcho_equation_thirteen (percepts : ℕ → Unit) (n : ℕ) :
    namedEcho.namedQValue (namedEcho.namedRun percepts [] n).2
        (namedEcho.act (namedEcho.namedRun percepts [] n).1 (namedEcho.namedRun percepts [] n).2) =
      namedEcho.namedQValue (namedEcho.namedRun percepts [] n).2
        (namedEcho.act namedEcho.initial (namedEcho.namedRun percepts [] n).2) :=
  NamedModel.named_equation_thirteen namedEcho percepts [] n

/-- The embedding of the name-erasing model keeps its `Q` values. -/
theorem alternatingModel_toNamed_namedQValue :
    alternatingModel.toNamed.namedQValue = alternatingModel.qValue :=
  Model.toNamed_namedQValue alternatingModel

/-- **Equation (13) with names in the history**, at the embedded nontrivial
model, together with the one-step and induction lemmas it rests on. -/
theorem alternatingModel_toNamed_equation_thirteen (percepts : ℕ → Bool) (start : Bool) (n : ℕ) :
    alternatingModel.toNamed.namedQValue (alternatingModel.toNamed.namedRun percepts start n).2
        (alternatingModel.toNamed.act (alternatingModel.toNamed.namedRun percepts start n).1
          (alternatingModel.toNamed.namedRun percepts start n).2) =
      alternatingModel.toNamed.namedQValue (alternatingModel.toNamed.namedRun percepts start n).2
        (alternatingModel.toNamed.act alternatingModel.toNamed.initial
          (alternatingModel.toNamed.namedRun percepts start n).2) :=
  NamedModel.named_equation_thirteen alternatingModel.toNamed percepts start n

/-- The named one-step argument, induction step and run lemma, at the witness. -/
theorem namedEcho_step_lemmas (p : Bool) (h : List ((Bool × Bool) × Unit)) (e : Unit) :
    namedEcho.contValue p h ≤ namedEcho.contValue namedEcho.initial h ∧
      namedEcho.contValue p h = namedEcho.namedQValue h (namedEcho.act p h) ∧
      namedEcho.NamedOptimalAt namedEcho.initial h ∧
      (namedEcho.contValue (namedEcho.act namedEcho.initial h).2
          (namedEcho.extend h (namedEcho.act namedEcho.initial h) e) =
        namedEcho.contValue namedEcho.initial
          (namedEcho.extend h (namedEcho.act namedEcho.initial h) e)) ∧
      namedEcho.NamedOptimalAt (namedEcho.act namedEcho.initial h).2
        (namedEcho.extend h (namedEcho.act namedEcho.initial h) e) ∧
      (∀ percepts : ℕ → Unit, ∀ n, namedEcho.NamedOptimalAt (namedEcho.namedRun percepts h n).1
        (namedEcho.namedRun percepts h n).2) :=
  ⟨NamedModel.namedContValue_le_initial namedEcho p h,
    NamedModel.namedContValue_eq_qValue namedEcho p h,
    NamedModel.namedOptimalAt_initial namedEcho h,
    NamedModel.named_selected_matches_initial namedEcho (NamedModel.namedOptimalAt_initial namedEcho h) e,
    NamedModel.namedOptimalAt_next namedEcho (NamedModel.namedOptimalAt_initial namedEcho h) e,
    fun percepts => NamedModel.namedRun_optimal namedEcho percepts h⟩


/-! ## Wave 4: Definition 12 without an optimal name, and equation (7) for every policy

`nameReader` is a `RealisticModel` in which the world action is the last recorded
name, world action `true` pays `1` and `false` pays `0`. The value of a named
policy reads the recorded name, so no modification-independence holds, and no
named policy is optimal at the empty history, so it is no `NamedModel`. Print's
Definition 12 still defines its values.
-/

/-- The pay of the last recorded world action, `0` on the empty history. -/
def lastPay : List ((Bool × Bool) × Unit) → ℝ := fun h ↦
  match h.getLast? with
  | some ((true, _), _) => 1
  | _ => 0

/-- The pay after a step is that step's world action's pay. -/
theorem lastPay_snoc (h : List ((Bool × Bool) × Unit)) (w q : Bool) (e : Unit) :
    lastPay (h ++ [((w, q), e)]) = if w then 1 else 0 := by
  cases w <;> simp [lastPay]

/-- The last recorded name after a step is that step's name. -/
theorem lastName_snoc (h : List ((Bool × Bool) × Unit)) (w q : Bool) (e : Unit) :
    lastName (h ++ [((w, q), e)]) = q := by
  simp [lastName]

/-- A Definition 12 model whose named policies replay the last recorded name. -/
noncomputable def nameReader : RealisticModel (List ((Bool × Bool) × Unit)) Bool Bool Unit where
  act := fun p h ↦ (lastName h, p)
  extend := fun h a e ↦ h ++ [(a, e)]
  utility := lastPay
  discount := 1 / 2
  discount_pos := by norm_num
  prob := fun _ _ _ ↦ 1
  prob_sum_one := by intro h a; simp
  prob_pos := by intro h a e; norm_num
  contValue := fun p h ↦ (if lastName h then 1 else 0) + (if p then 1 else 0)
  bellman := by
    intro p h
    simp only [lastPay_snoc, lastName_snoc]
    cases p <;> cases lastName h <;> simp <;> norm_num

/-- The value of a named policy reads the recorded name: two histories that
differ only in it get different values. -/
theorem nameReader_contValue_reads_name :
    nameReader.contValue false [((false, true), ())] ≠
      nameReader.contValue false [((false, false), ())] := by
  simp [nameReader, lastName]

/-- No named policy is optimal at the empty history. -/
theorem nameReader_no_optimal_name (p : Bool) : ¬ RealisticModel.OptimalAt nameReader p [] := by
  intro hopt
  have h := hopt (true, true)
  cases p <;>
    simp [RealisticModel.qValue, nameReader, lastPay, lastName] at h <;> norm_num at h

/-- An unnamed policy: always play `true` and install the name `true`. -/
def alwaysTrue : Policy (List ((Bool × Bool) × Unit)) Bool Bool := fun _ ↦ (true, true)

/-- `alwaysTrue` has no name in `nameReader`. -/
theorem alwaysTrue_unnamed (p : Bool) : nameReader.act p ≠ alwaysTrue := by
  intro h
  have := congrFun h []
  simp [nameReader, alwaysTrue, lastName] at this

/-- **Equation (7) at an unnamed policy**: its realistic value at the empty history. -/
theorem nameReader_realisticValue_alwaysTrue :
    nameReader.realisticValue alwaysTrue [] = 2 := by
  simp [RealisticModel.realisticValue, RealisticModel.qValue, nameReader, alwaysTrue, lastPay,
    lastName]
  norm_num

/-- Equation (7) at a named policy is its continuation value, at the witness. -/
theorem nameReader_realisticValue_name (p : Bool) (h : List ((Bool × Bool) × Unit)) :
    nameReader.realisticValue (nameReader.act p) h = nameReader.contValue p h ∧
      nameReader.contValue p h = nameReader.qValue h (nameReader.act p h) :=
  ⟨RealisticModel.realisticValue_name nameReader p h,
    RealisticModel.contValue_eq_qValue nameReader p h⟩

/-- The projection of a `NamedModel` keeps its `Q` values, and its realistic value
at a named policy is the continuation value, at the name-reading model. -/
theorem namedEcho_toRealistic (p : Bool) (h : List ((Bool × Bool) × Unit)) :
    (NamedModel.toRealistic namedEcho).qValue = namedEcho.namedQValue ∧
      NamedModel.realisticValue namedEcho (namedEcho.act p) h = namedEcho.contValue p h :=
  ⟨NamedModel.toRealistic_qValue namedEcho, NamedModel.realisticValue_name namedEcho p h⟩

/-! ## Wave 4: modification-independence of `V₁^{re,π₁}` derived

`alternatingChecked` is `alternatingModel` with the selected names recorded in
the history and the check-projection erasing them. -/

/-- The utility of a check-history: the pay of its last world action. -/
noncomputable def checkPay : List (Bool × Bool) → ℝ := fun c ↦
  match c.getLast? with
  | some (true, _) => 0
  | _ => 1 / 2

/-- Erase the policy names from a history. -/
def eraseNames : List ((Bool × ℕ) × Bool) → List (Bool × Bool) :=
  List.map fun x ↦ (x.1.1, x.2)

/-- `alternatingModel` with names recorded, at print's Theorem 16 hypotheses. -/
noncomputable def alternatingChecked :
    ModIndepModel (List ((Bool × ℕ) × Bool)) Bool ℕ Bool (List (Bool × Bool)) where
  act := fun p _ => if p = 0 then (false, 1) else if p = 1 then (false, 0) else (true, p)
  extend := fun h a e ↦ h ++ [(a, e)]
  utility := fun h ↦ checkPay (eraseNames h)
  discount := 1 / 2
  discount_pos := by norm_num
  prob := fun _ _ _ => 1 / 2
  prob_sum_one := by intro h a; simp
  prob_pos := by intro h a e; norm_num
  contValue := fun p _ => if p ≤ 1 then 1 else 0
  bellman := by
    intro p h
    match p with
    | 0 => simp [eraseNames, checkPay]; norm_num
    | 1 => simp [eraseNames, checkPay]; norm_num
    | (n + 2) => simp [eraseNames, checkPay]
  initial := 0
  initial_optimal := by
    rintro h ⟨w, q⟩
    cases w <;> simp [eraseNames, checkPay] <;> split_ifs <;> norm_num
  check := eraseNames
  check_extend := by
    intro h h' w p p' e hc
    simp [eraseNames] at hc ⊢
    exact hc
  prob_check := fun _ _ _ ↦ rfl
  utility_check := fun _ _ hc ↦ by simp only [hc]
  discount_lt_one := by norm_num
  initial_bounded := ⟨1, fun _ ↦ by simp⟩

/-- **`V₁^{re,π₁}` is modification-independent**, derived at the witness, with the
induction step of Theorem 16 it feeds. -/
theorem alternatingChecked_modIndep (h : List ((Bool × ℕ) × Bool)) (w : Bool) (p p' : ℕ)
    (e : Bool) :
    alternatingChecked.contValue alternatingChecked.initial (alternatingChecked.extend h (w, p) e) =
        alternatingChecked.contValue alternatingChecked.initial
          (alternatingChecked.extend h (w, p') e) ∧
      alternatingChecked.utility (alternatingChecked.extend h (w, p) e) =
        alternatingChecked.utility (alternatingChecked.extend h (w, p') e) ∧
      alternatingChecked.contValue p h ≤
        alternatingChecked.contValue alternatingChecked.initial h :=
  ⟨ModIndepModel.initial_modIndep alternatingChecked h w p p' e,
    ModIndepModel.utility_modIndep alternatingChecked h w p p' e,
    ModIndepModel.contValue_le_initial alternatingChecked p h⟩

/-- `check`-equal histories have the same initial value, at the witness. -/
theorem alternatingChecked_initial_check (x x' : List ((Bool × ℕ) × Bool))
    (hx : alternatingChecked.check x = alternatingChecked.check x') :
    alternatingChecked.contValue alternatingChecked.initial x =
      alternatingChecked.contValue alternatingChecked.initial x' :=
  ModIndepModel.initial_check alternatingChecked x x' hx

/-- **The induction step of Theorem 16** at the witness, from the initial policy. -/
theorem alternatingChecked_optimalAt_next (h : List ((Bool × ℕ) × Bool)) (e : Bool)
    (hopt : RealisticModel.OptimalAt alternatingChecked.toRealisticModel alternatingChecked.initial h) :
    alternatingChecked.OptimalAt (alternatingChecked.act alternatingChecked.initial h).2
      (alternatingChecked.extend h (alternatingChecked.act alternatingChecked.initial h) e) :=
  ModIndepModel.optimalAt_next alternatingChecked hopt e

/-- The initial policy is optimal at the witness, so the induction step applies. -/
theorem alternatingChecked_initial_optimalAt (h : List ((Bool × ℕ) × Bool)) :
    alternatingChecked.OptimalAt alternatingChecked.initial h :=
  NamedModel.namedOptimalAt_initial (ModIndepModel.toNamedModel alternatingChecked) h


/-- A name-reading policy inside the carrier: `namedEcho` at print's Theorem 16
hypotheses, with the check-projection erasing names. Its world action is the
last recorded name. -/
noncomputable def namedEchoChecked :
    ModIndepModel (List ((Bool × Bool) × Unit)) Bool Bool Unit (List (Bool × Unit)) where
  act := fun p h ↦ (lastName h, p)
  extend := fun h a e ↦ h ++ [(a, e)]
  utility := fun _ ↦ 0
  discount := 1 / 2
  discount_pos := by norm_num
  prob := fun _ _ _ ↦ 1
  prob_sum_one := by intro h a; simp
  prob_pos := by intro h a e; norm_num
  contValue := fun _ _ ↦ 0
  bellman := by intro p h; simp
  initial := false
  initial_optimal := by intro h a; simp
  check := List.map fun x ↦ (x.1.1, x.2)
  check_extend := by
    intro h h' w p p' e hc
    simp only [List.map_append, List.map_cons, List.map_nil] at hc ⊢
    rw [hc]
  prob_check := fun _ _ _ ↦ rfl
  utility_check := fun _ _ _ ↦ rfl
  discount_lt_one := by norm_num
  initial_bounded := ⟨0, fun _ ↦ by simp⟩

/-- The name-reading witness: its policy reads the recorded name, and the induction
step applies to it. -/
theorem namedEchoChecked_reads_name_and_step (h : List ((Bool × Bool) × Unit)) (e : Unit) :
    (namedEchoChecked.act false [((false, true), ())]).1 = true ∧
      RealisticModel.OptimalAt namedEchoChecked.toRealisticModel
        (namedEchoChecked.act namedEchoChecked.initial h).2
        (namedEchoChecked.extend h (namedEchoChecked.act namedEchoChecked.initial h) e) :=
  ⟨rfl, ModIndepModel.optimalAt_next namedEchoChecked
    (NamedModel.namedOptimalAt_initial (ModIndepModel.toNamedModel namedEchoChecked) h) e⟩

/-! `Model` lemmas named in full: their leaf names are shared with `RealisticModel` and
`ModIndepModel`. -/
example (p h) :=
  AISafetyAtlas.Wireheading.GoalPreservationRun.Model.contValue_le_initial alternatingModel p h
example (p h) :=
  AISafetyAtlas.Wireheading.GoalPreservationRun.Model.contValue_eq_qValue alternatingModel p h
example (h e) :=
  AISafetyAtlas.Wireheading.GoalPreservationRun.Model.optimalAt_next alternatingModel
    (AISafetyAtlas.Wireheading.GoalPreservationRun.Model.optimalAt_initial alternatingModel h) e

end AISafetyAtlas.Examples.Wireheading.GoalPreservationRun
