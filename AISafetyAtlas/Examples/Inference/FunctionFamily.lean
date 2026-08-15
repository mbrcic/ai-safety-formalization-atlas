module

public import AISafetyAtlas.Inference

/-!
# Worked model: a reality containing every admissible Boolean function

The 2018 paper, after Definition 10:

> *"Prop. 7(ii) means that no reality with `|U| > 3` can have a universal device
> if the reality contains all functions defined over `U`."*

`FullReality.not_isUniversalFull_of_containsEveryTwoValuedBool` proves the
conclusion. Until now its hypothesis had **no model anywhere in the tree** —
`ContainsEveryTwoValuedBool` occurred exactly twice, at its own definition and at
that one theorem. A load-bearing hypothesis with no inhabitant is the failure
mode the *"positive hypotheses still without a witness"* section of the 2008 map
exists to catch, and it is sharper here than usual: clash 28's whole argument is
that the richness hypothesis is what carries the result, since a reality with an
**empty** function family satisfies the second universality clause vacuously.

The nearest existing model, `Device.conclInFamilyReality`, does not close it. Its
family is the single map `id`, not every surjective `Bool → Bool`, and it lives
at `U = Bool`, so it cannot exercise the printed `|U| > 3` regime at all.

Here `U = Fin 4`, so `|U| = 4 > 3` — the printed regime, for the first time.

**The family is indexed by a subtype, not enumerated.** Taking
`B := {f : Fin 4 → Bool // Function.Surjective f}` and `funcOf := Subtype.val`
makes `ContainsEveryTwoValuedBool` hold by construction. Enumerating instead
would mean listing all fourteen surjective maps `Fin 4 → Bool` (`2⁴ − 2`), which
proves the same thing at fourteen times the length.

**Why *surjective* and not *all*.** *"All functions defined over `U`"* cannot be
read type-theoretically: the constant maps are functions `Fin 4 → Bool`, and a
reality containing one fails `SourceStipulations.func_two`, the paper's own
stipulation that every function considered takes at least two values. The
subtype is the source's reading, and `stipulations` below proves the reality
satisfies all four stipulations rather than asserting it.
-/

namespace AISafetyAtlas.Examples.Inference.FunctionFamily

open AISafetyAtlas.Inference

/-- Every surjective Boolean function on `Fin 4`, as an index type. -/
public abbrev TwoValued : Type := {f : Fin 4 → Bool // Function.Surjective f}

/-- A conclusion function on `Fin 4`: the low half against the high half. -/
@[expose] public def splitConcl : Fin 4 → Bool := fun u => decide (u.val < 2)

public theorem splitConcl_surjective : Function.Surjective splitConcl := by
  intro b
  cases b with
  | true => exact ⟨0, rfl⟩
  | false => exact ⟨2, rfl⟩

/-- One device, and **every** admissible Boolean function, over `Fin 4`. -/
@[expose] public def everyFunctionReality :
    FullReality (Fin 4) (fun _ : Unit => Fin 4) (fun _ : TwoValued => Bool) where
  setupOf := fun _ => id
  conclOf := fun _ => splitConcl
  funcOf := Subtype.val

public theorem everyFunctionReality_surj :
    ∀ α : Unit, Function.Surjective (everyFunctionReality.conclOf α) :=
  fun _ => splitConcl_surjective

/-- The hypothesis of the printed conclusion, inhabited. By construction: the
index type *is* the set of admissible functions. -/
public theorem everyFunctionReality_containsEvery :
    everyFunctionReality.ContainsEveryTwoValuedBool :=
  fun Γ hΓ => ⟨⟨Γ, hΓ⟩, rfl⟩

/-- **The printed sentence, on a universe the printed sentence is about.**
`|U| = 4 > 3`, the family contains every admissible function, and no device of
the reality is universal. The cardinality plays no part in the proof — see
clash 28 — but this is the first model in which it holds. -/
public theorem everyFunctionReality_not_universal (α : Unit) :
    ¬ everyFunctionReality.IsUniversalFull everyFunctionReality_surj α :=
  everyFunctionReality.not_isUniversalFull_of_containsEveryTwoValuedBool
    everyFunctionReality_surj everyFunctionReality_containsEvery α

/-- Four elements, so the printed `\|U\| > 3` is genuinely met. -/
public theorem card_universe : Fintype.card (Fin 4) = 4 := by decide

/-- **Non-degeneracy.** The reality meets all four of the source's standing
stipulations, so the model is not admitted by dropping the conventions the
paper works under. `func_two` is where the subtype earns its keep: a surjective
map onto `Bool` takes two values by definition. -/
public theorem stipulations : everyFunctionReality.SourceStipulations where
  family_nonempty := ⟨Sum.inl ()⟩
  concl_surj := everyFunctionReality_surj
  setup_two := fun _ => ⟨0, 1, by simp [everyFunctionReality]⟩
  func_two := by
    intro β
    obtain ⟨u, hu⟩ := β.2 true
    obtain ⟨u', hu'⟩ := β.2 false
    exact ⟨u, u', by simp [everyFunctionReality, hu, hu']⟩

/-! ## A reality that **does** have a universal device

`IsUniversalFull` had no positive model: every use in the tree was a `¬`. A
definition only ever refuted is one nothing is known to satisfy, and the
uniqueness theorem `isUniversalFull_unique` then quantifies over nothing.

The reality below has one device and one extra function, so clause 1 —
*"strongly infers all other devices"* — is vacuous. Clause 2 is not: the device
really does weakly infer the reality's function, and by Proposition 1(ii) that
function cannot be its own conclusion, so the model has to separate them. It
does: the conclusion splits `Fin 4` in half and the function alternates.
-/

/-- The reality's one extra function, deliberately **not** the conclusion. -/
public abbrev altFunc : Fin 4 → Bool := ![true, false, true, false]

/-- One device, one function, over four states. -/
public def universalReality :
    FullReality (Fin 4) (fun _ : Unit => Fin 4) (fun _ : Unit => Bool) where
  setupOf := fun _ => id
  conclOf := fun _ => splitConcl
  funcOf := fun _ => altFunc

public theorem universalReality_surj :
    ∀ α : Unit, Function.Surjective (universalReality.conclOf α) :=
  fun _ => splitConcl_surjective

/-- The identity setup makes each fibre a single state, so a probe is answered
wherever the conclusion happens to match it — and here both probes are matched
somewhere, at `0` and at `1`. -/
public theorem universalReality_weaklyInfers :
    WeaklyInfers (universalReality.device universalReality_surj ()) altFunc := by
  simp only [universalReality, FullReality.device, deviceOf, WeaklyInfers,
    InferenceDevice.Realized]
  intro γ f hf _
  cases γ with
  | true =>
    refine ⟨0, ⟨0, rfl⟩, fun w hw => ?_⟩
    have : w = 0 := hw
    subst this
    exact ((hf true).mpr rfl).symm
  | false =>
    refine ⟨1, ⟨1, rfl⟩, fun w hw => ?_⟩
    have : w = 1 := hw
    subst this
    exact ((hf false).mpr rfl).symm

/-- **`IsUniversalFull` is inhabited.** Clause 1 holds vacuously — there is one
device — and clause 2 holds substantively. -/
public theorem universalReality_isUniversalFull :
    universalReality.IsUniversalFull universalReality_surj () :=
  ⟨fun α' hne => absurd (Subsingleton.elim α' ()) hne,
    fun _ => universalReality_weaklyInfers⟩

/-- And the printed uniqueness claim is exercised on something that exists,
rather than quantifying over an empty predicate. -/
public theorem universalReality_unique (α : Unit) :
    universalReality.IsUniversalFull universalReality_surj α → α = () :=
  fun _ => Subsingleton.elim α ()


/-- **The universal-device model is source-admissible too.** Non-empty family,
surjective conclusion, a two-valued setup map and a two-valued extra function —
all four of the paper's standing stipulations, certified rather than evident. -/
public theorem universalReality_stipulations :
    universalReality.SourceStipulations where
  family_nonempty := ⟨Sum.inl ()⟩
  concl_surj := universalReality_surj
  setup_two := fun _ => ⟨0, 1, by simp [universalReality]⟩
  func_two := fun _ => ⟨0, 1, by simp [universalReality]⟩

end AISafetyAtlas.Examples.Inference.FunctionFamily
