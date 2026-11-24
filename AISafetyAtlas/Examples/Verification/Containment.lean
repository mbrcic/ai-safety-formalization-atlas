module

public import AISafetyAtlas.Verification.Containment

/-!
# Print's *HaltHarm* actually exists

This example witnesses that the `HarmReduction` certificate required by
`AISafetyAtlas.Verification.Containment.harming_undecidable` is realizable, and
realizes it the way print's Assumption 2 says it is realizable: by **simulating
a universal machine**.

`harms R D` here is *`R` run on `D` eventually performs its effect*, modelled as
`R` halting on `D`. Print's *HarmHumans()* is an opaque operation that *"harms
humans and takes a finite time"*, so the composite `execute T(I); execute
HarmHumans()` performs its effect exactly when `T(I)` halts — which is the
biconditional print's proof uses, and is what `haltHarm_harms_iff` proves.

The witness is not the identity. *haltHarmCode* is extracted from
*Nat.Partrec.Code.exists_code* applied to the universal evaluation function, so
it is a genuine program that decodes its input as a machine and runs it. That is
Assumption 2's *"`R` must be able to simulate a universal Turing machine"* doing
the one job the proof needs it for.

The fixed-input half of this file adds no public atlas declarations. The
later parts do (the last one witnesses `Assumption2Harm`, print's Assumption 2
with *HarmHumans()* as a clause): print's Assumption 2 is a statement in the tree as of
2026-09-20, so the witness that satisfies it has to be nameable. No part
claims that halting models harm; each demonstrates the computability mechanism.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Examples.Verification.Containment

open AISafetyAtlas.Verification.Containment

/-- *"`R` run on `D` performs its effect"*, modelled as halting. -/
private def haltsOn (program : Code) (data : Code) : Prop :=
  (eval program (Encodable.encode data)).Dom

/-- The universal simulation print's Assumption 2 asks for, as a partial function. -/
private theorem simulate_partrec (input : ℕ) :
    Nat.Partrec fun d : ℕ => eval (Denumerable.ofNat Code d) input :=
  Partrec.nat_iff.mp (eval_part.comp (Computable.ofNat Code) (Computable.const input))

/-- Print's *HaltHarm()*: decode the input as a machine, run it on `input`. -/
private noncomputable def haltHarmCode (input : ℕ) : Code :=
  (exists_code.mp (simulate_partrec input)).choose

private theorem haltHarmCode_eval (input : ℕ) :
    eval (haltHarmCode input) = fun d : ℕ => eval (Denumerable.ofNat Code d) input :=
  (exists_code.mp (simulate_partrec input)).choose_spec

/-- The composite performs its effect exactly when the simulated machine halts. -/
private theorem haltHarm_harms_iff (input : ℕ) (source : Code) :
    haltsOn (haltHarmCode input) source ↔ (eval source input).Dom := by
  simp [haltsOn, haltHarmCode_eval]

private noncomputable def universalReduction (input : ℕ) : HarmReduction haltsOn where
  haltHarm := haltHarmCode input
  sourceInput := input
  encode := id
  computable_encode := Computable.id
  harms_iff_halts := haltHarm_harms_iff input

example (input : ℕ) : ¬ Nonempty (HarmDecider haltsOn) :=
  harming_undecidable (universalReduction input)

/-! ## Print's Assumption 2, satisfied by print's own composite

The reduction above fixes the input. Print's data is the pair `(T, I)`, and
print's Assumption 2 asks the composite to *simulate a universal Turing
machine* on it. `Assumption2` states that; what follows satisfies it, with the
composite extracted the same way — from *Nat.Partrec.Code.exists_code* applied
to an evaluation function, now one that unpairs its input into a machine and an
input for it.
-/

/-- Print's `D = (T, I)`, packaged as one number. -/
private def encodePair (p : Code × ℕ) : ℕ := Nat.pair (Encodable.encode p.1) p.2

private theorem computable_encodePair : Computable encodePair :=
  (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) Primrec.snd).to_comp

private theorem injective_encodePair : Function.Injective encodePair := by
  rintro ⟨s, i⟩ ⟨t, j⟩ h
  have h2 := congrArg Nat.unpair h
  simp only [encodePair, Nat.unpair_pair, Prod.mk.injEq] at h2
  exact Prod.ext (Encodable.encode_injective h2.1) h2.2

/-- The universal simulation on a packaged pair: decode the first component as a
machine and run it on the second. -/
private theorem simulatePair_partrec :
    Nat.Partrec fun d : ℕ =>
      eval (Denumerable.ofNat Code (Nat.unpair d).1) (Nat.unpair d).2 :=
  Partrec.nat_iff.mp (eval_part.comp
    ((Computable.ofNat Code).comp (Primrec.fst.comp Primrec.unpair).to_comp)
    (Primrec.snd.comp Primrec.unpair).to_comp)

/-- Print's *HaltHarm()* at print's own quantifier. -/
private noncomputable def haltHarmPairCode : Code :=
  (exists_code.mp simulatePair_partrec).choose

private theorem haltHarmPairCode_eval :
    eval haltHarmPairCode =
      fun d : ℕ => eval (Denumerable.ofNat Code (Nat.unpair d).1) (Nat.unpair d).2 :=
  (exists_code.mp simulatePair_partrec).choose_spec

private theorem assumption2_haltHarmPairCode : Assumption2 haltHarmPairCode encodePair where
  simulates := fun source input => by
    simp [haltHarmPairCode_eval, encodePair, Nat.unpair_pair, Denumerable.ofNat_encode]
  covers := injective_encodePair
  computable_encode := computable_encodePair

/-- **Print's Assumption 2 is inhabited**, by a composite that really does
decode its input as a machine and run it — Assumption 2's own *"must be able to
simulate a universal Turing machine"*, doing the one job print's proof needs it
for. -/
public theorem exists_assumption2 :
    ∃ (haltHarm : Code) (encode : Code × ℕ → ℕ), Assumption2 haltHarm encode :=
  ⟨haltHarmPairCode, encodePair, assumption2_haltHarmPairCode⟩

/-- **Theorem 1, fired from print's Assumption 2 alone**, at the effect relation
print's Algorithm 3 has. -/
public theorem harming_undecidable_at_universal : ¬ Nonempty (HarmDecider HaltsOn) := by
  obtain ⟨haltHarm, encode, assumption⟩ := exists_assumption2
  exact harming_undecidable_of_assumption2 assumption

/-- The two source problems, at the witness: print's reduction over pairs gives
the fixed-input one the earlier theorem consumes. -/
public theorem exists_harmReductionPair : Nonempty (HarmReductionPair HaltsOn) :=
  ⟨assumption2_haltHarmPairCode.harmReductionPair⟩

/-- The halting problem at both arguments, which is the shape print's `D = (T, I)`
ranges over. -/
public theorem halting_problem_pair_holds :
    ¬ ComputablePred fun p : Code × ℕ => (eval p.1 p.2).Dom :=
  halting_problem_pair

/-! ## Print's Assumption 2 with *HarmHumans()* as a clause

The same universal composite, now with print's last sentence: *HarmHumans()* is
`Code.zero`, which takes a finite time, and the effect relation is `HaltsOn`,
under which it harms. The observation's second half then holds by definition. -/

private theorem assumption2Harm_zero :
    Assumption2Harm HaltsOn Code.zero haltHarmPairCode encodePair where
  toAssumption2 := assumption2_haltHarmPairCode
  total := fun _ => trivial
  harmful := fun _ => trivial

/-- **Print's Assumption 2, last sentence included, is inhabited**, at the
universal composite and a total *HarmHumans()*. -/
public theorem exists_assumption2Harm :
    ∃ (harmHumans universal : Code) (encode : Code × ℕ → ℕ),
      Assumption2Harm HaltsOn harmHumans universal encode :=
  ⟨Code.zero, haltHarmPairCode, encodePair, assumption2Harm_zero⟩

/-- **Theorem 1 from print's Assumption 2 with *HarmHumans()*,** fired at the
witness: the observation's second half holds for `HaltsOn` by definition. -/
public theorem harming_undecidable_at_assumption2Harm :
    ¬ Nonempty (HarmDecider HaltsOn) :=
  harming_undecidable_of_assumption2Harm assumption2Harm_zero fun _ => Iff.rfl

/-! Direct instantiations under qualified names: the leaf `harmReductionPair` is
shared by `Assumption2` and `Assumption2Harm`, so dot-notation uses do not say
which one they reach. -/

noncomputable example : HarmReductionPair HaltsOn :=
  AISafetyAtlas.Verification.Containment.Assumption2.harmReductionPair
    assumption2_haltHarmPairCode

noncomputable example : HarmReductionPair HaltsOn :=
  AISafetyAtlas.Verification.Containment.Assumption2Harm.harmReductionPair
    assumption2Harm_zero fun _ => Iff.rfl

example (source : Code) (input : ℕ) :
    (eval (haltHarmOf Code.zero haltHarmPairCode) (encodePair (source, input))).Dom ↔
      (eval source input).Dom :=
  AISafetyAtlas.Verification.Containment.Assumption2Harm.haltHarm_dom_iff
    assumption2Harm_zero source input

example (source : Code) (input : ℕ) :
    (eval haltHarmPairCode (encodePair (source, input))).Dom ↔ (eval source input).Dom :=
  AISafetyAtlas.Verification.Containment.Assumption2Harm.harmHumans_executed_iff
    assumption2Harm_zero source input

/-! ## Print's isolation premise, satisfied

`HaltsOn` cannot meet `SequentialHarm`: under it the universal machine harms
wherever it halts, against print's *"a Turing machine is isolated"*. The relation
below meets it. *HarmHumans()* is `Code.zero` and harms on every input, the
composite harms exactly where its first step returns, and nothing else harms,
in particular not the universal machine. -/

/-- An effect relation obeying print's isolation premise: only *HarmHumans()*
and the composite that reaches it harm. -/
private def isolatedHarm (program : Code) (data : ℕ) : Prop :=
  program = Code.zero ∨
    (program = haltHarmOf Code.zero haltHarmPairCode ∧ (eval haltHarmPairCode data).Dom)

/-- The universal composite is not *HarmHumans()*: on the packaged `(succ, 0)` it
returns `1`, and `Code.zero` returns `0` everywhere. -/
private theorem haltHarmPairCode_ne_zero : haltHarmPairCode ≠ Code.zero := by
  intro h
  have hsim := assumption2_haltHarmPairCode.simulates Code.succ 0
  rw [h] at hsim
  have h1 : (1 : ℕ) ∈ eval Code.zero (encodePair (Code.succ, 0)) := by
    rw [hsim]; simp [eval]
  change (1 : ℕ) ∈ Part.some 0 at h1
  simp at h1

private theorem haltHarmOf_ne_haltHarmPairCode :
    haltHarmOf Code.zero haltHarmPairCode ≠ haltHarmPairCode := by
  intro h
  have := congrArg sizeOf h
  simp [haltHarmOf] at this

private theorem not_isolatedHarm_universal (d : ℕ) : ¬ isolatedHarm haltHarmPairCode d := by
  rintro (h | ⟨h, _⟩)
  · exact haltHarmPairCode_ne_zero h
  · exact haltHarmOf_ne_haltHarmPairCode h.symm

private theorem assumption2Harm_isolated :
    Assumption2Harm isolatedHarm Code.zero haltHarmPairCode encodePair where
  toAssumption2 := assumption2_haltHarmPairCode
  total := fun _ => trivial
  harmful := fun _ => Or.inl rfl

private theorem sequentialHarm_isolatedHarm :
    SequentialHarm isolatedHarm Code.zero haltHarmPairCode encodePair where
  isolated := fun _ _ => not_isolatedHarm_universal _
  seq := fun d => by
    have hne : haltHarmOf Code.zero haltHarmPairCode ≠ Code.zero := by
      simp [haltHarmOf]
    rw [or_iff_right (not_isolatedHarm_universal d)]
    simp only [isolatedHarm, hne, false_or, true_and]
    exact ⟨fun h => ⟨_, Part.get_mem h, Or.inl trivial⟩,
      fun ⟨y, hy, _⟩ => Part.dom_iff_mem.mpr ⟨y, hy⟩⟩

/-- **Print's isolation semantics is satisfiable**, together with Assumption 2
with *HarmHumans()*, at the universal composite. -/
public theorem exists_sequentialHarm :
    ∃ (harms : Code → ℕ → Prop) (harmHumans universal : Code) (encode : Code × ℕ → ℕ),
      Assumption2Harm harms harmHumans universal encode ∧
        SequentialHarm harms harmHumans universal encode :=
  ⟨isolatedHarm, Code.zero, haltHarmPairCode, encodePair, assumption2Harm_isolated,
    sequentialHarm_isolatedHarm⟩

/-- **Theorem 1 from print's premises, at an effect relation that is not
halting**: the universal machine halts on some packaged `(T, I)` without harming,
and still no `Harm` decider exists. The reduction is built from the isolation
semantics, not from `HaltsOn`. -/
public theorem harming_undecidable_isolated :
    ∃ harms : Code → ℕ → Prop,
      (∃ program data, (eval program data).Dom ∧ ¬ harms program data) ∧
        ¬ Nonempty (HarmDecider harms) := by
  refine ⟨isolatedHarm, ⟨haltHarmPairCode, encodePair (Code.zero, 0), ?_,
    not_isolatedHarm_universal _⟩, harming_undecidable_pair
    (AISafetyAtlas.Verification.Containment.SequentialHarm.toHarmReductionPair
      sequentialHarm_isolatedHarm assumption2Harm_isolated)⟩
  rw [assumption2_haltHarmPairCode.simulates]
  trivial

example (source : Code) (input : ℕ) :
    isolatedHarm (haltHarmOf Code.zero haltHarmPairCode) (encodePair (source, input)) ↔
      (eval haltHarmPairCode (encodePair (source, input))).Dom :=
  AISafetyAtlas.Verification.Containment.SequentialHarm.harms_iff_executed
    sequentialHarm_isolatedHarm assumption2Harm_isolated source input

example (source : Code) (input : ℕ) :
    isolatedHarm (haltHarmOf Code.zero haltHarmPairCode) (encodePair (source, input)) ↔
      (eval source input).Dom :=
  AISafetyAtlas.Verification.Containment.SequentialHarm.harms_haltHarmOf_iff_halts
    sequentialHarm_isolatedHarm assumption2Harm_isolated source input

end AISafetyAtlas.Examples.Verification.Containment
