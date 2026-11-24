module

public import AISafetyAtlas.Verification

/-!
# The harming problem, and why deciding it would decide halting

This module carries **Theorem 1** of Alfonseca, Cebrian, Fernández Anta,
Coviello, Abeliuk and Rahwan, *Superintelligence Cannot be Contained: Lessons
from Computability Theory*, **J. Artificial Intelligence Research 70 (2021)
65–76** — the published text, not a preprint. Journal page 71 is the source of
every quotation below.

## What print states

**Algorithm 3**, *HaltHarm(T, I)*: *input:* Turing machine `T`, input `I`;
*execute* `T(I)`; *execute* *HarmHumans()*; *end*.

**Theorem 1.** *The harming problem is undecidable.*

The proof is one substitution. Assume `Harm(R, D)` is computable for every
program `R` and input `D`. Take *R = HaltHarm()* and `D = (T, I)`. Then, in
print's words, *"*Harm(HaltHarm(), (T, I))* returns `TRUE` if and only if
*HaltHarm(T, I)* harms humans. Hence, *Harm(HaltHarm(), (T, I))* returns `TRUE`
if and only if `T(I)` halts."*

Note which argument moves: the **program is fixed** at *HaltHarm* and the
**data varies** over `(T, I)`. `harming_undecidable` moves the same one.

## What is formalized, and what is deliberately not

`HarmReduction` is print's Assumption 2 reduced to the only thing the proof
consumes. Print's Assumption 2 reads: *"As the program `R` and the state of the
world `D` are arbitrarily complex, `R` must be able to simulate a universal
Turing machine and `D` includes the set of inputs that can be executed by a
universal Turing machine. In addition, the language of `R` contains at least one
explicit operation *HarmHumans()* that harms humans and takes a finite time."*
The structure asks for exactly what that buys: a distinguished program, a
computable way to package a machine as data, and the biconditional print
derives. It does **not** ask for a universal machine, because the proof never
simulates one — Assumption 2 is what makes the composite *constructible*, and
constructibility is what `computable_encode` records. **Assumption 2 as printed
is stated too, since 2026-09-20**, as `Assumption2`; the two are kept apart on
purpose, one saying what print assumes and the other what print's proof uses.

***HarmHumans* is uninterpreted here, and that is print's situation too.** No
predicate in this file means *harms humans*; `harms` is an arbitrary relation
between programs and data. So the theorem is about an **arbitrary effect
predicate**, and the safety reading is the bridge, not the theorem. Print's own
*HarmHumans()* is an opaque operation of the language of `R`.

**Corollary 3 is not here.** Print states *"Corollary 3. The containment problem
is incomputable"* and derives it in running prose from Assumption 2 — *"the
impossibility of deciding whether a superintelligent machine `R` will harm
humans in the presence of a scenario `D` leads to the conclusion that the
containment problem cannot be computed"* — without a reduction. There is no
argument to transcribe, so nothing is claimed for it. Stating the complement of
`harms` and calling it containment would be inventing print's missing step.

## Two senses of *containment*, and this module carries neither

The word in the field means isolation: keep the system in a box, restrict its
channels, and the hard part is that it may act to get out. That is Lampson's
1973 confinement problem, and print surveys it at journal page 68 — a Faraday
cage, minimal communication channels, Yudkowsky's social-engineering result
against question-answering systems, a restriction to binary questions.

Print's own glossary at journal page 69 then defines something else: *"A
superintelligent machine is **containable** if there is a control strategy that
prevents its acting on the external world when there is a reason to predict that
`R(D)` will harm humans, and allows it otherwise."* That is **predict-then-gate**
— a harm predictor plus a switch on actions — and it is a property of a machine,
not a decision problem. **The escape half is dropped between the two pages**, and
Theorem 1 is about what remains.

So neither is carried here. Nothing in this module concerns recognizing a system
that is trying to breach an isolation boundary; the atlas has no channel, no
boundary, and no notion of acting on an external world at all. A reader who
arrives with the field's definition will over-read `harming_undecidable`.

## Scope against print

`harming_undecidable` fixes `sourceInput` and varies the machine, because that
is the shape of Mathlib's `ComputablePred` halting statement, where print
quantifies over every `T` and `I`. **Both forms are here as of 2026-09-20 and
they are not the same theorem.** `HarmReductionPair` is print's quantifier and
`harming_undecidable_pair` is Theorem 1 from it; `HarmReductionPair.toHarmReduction`
reduces it to the fixed-input form, which is the sentence this header used to
carry in prose — *the two are equivalent as undecidable source problems* — and
did not have as a declaration. The fixed-input theorem is the **stronger** one,
since its hypothesis asks less of the composite. `halting_problem_pair` is the
halting problem at both arguments, which Mathlib does not state.

`Assumption2` is print's Assumption 2 itself, in print's three clauses, and
`harming_undecidable_of_assumption2` is print's proof from it and nothing else.
`Assumption2Harm` adds print's last sentence, a total harming *HarmHumans()*, as
clauses for an arbitrary effect relation, and `harming_undecidable_of_assumption2Harm`
is Theorem 1 from it.
It is deliberately **stronger than the proof consumes**: its simulation clause
is an equality of partial functions, because a machine agreeing only on domains
would not be simulating, and print's *"takes a finite time"* is why the appended
operation neither diverges nor prunes. `HarmReduction` remains the weaker thing
the proof actually uses. `Verification.Robot` still narrows in the way this
module used to.

Source pin and grading: `docs/provenance/source-coverage-audit.md`, the Alfonseca
section; the PDF is pinned in
`SOURCES-2026-09-13-untriaged-survey-rows.md`.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Verification.Containment

/--
**Print's `Harm` decider.** A total computable procedure answering, for every
program and every input, whether that program on that input harms.

Both arguments are decided at once, which is print's *"`Harm(R, D)` is
computable for every possible program `R` and input `D`"*.
-/
public structure HarmDecider {Program Data : Type*} [Primcodable Program]
    [Primcodable Data] (harms : Program → Data → Prop) where
  /-- The decision procedure. -/
  decide : Program → Data → Bool
  /-- Total and computable in both arguments. -/
  computable_decide : Computable₂ decide
  /-- Sound and complete. -/
  correct : ∀ R D, ((decide R D : Prop) ↔ harms R D)

/--
**Print's Algorithm 3, abstracted to what its proof uses.**

*haltHarm* is the composite program *execute `T(I)`; execute *HarmHumans()**.
`encode` packages a machine as the data `(T, I)` at a fixed input, and
`harms_iff_halts` is the line print's proof turns on.

`computable_encode` is the clause that keeps this honest: without it the
reduction could be supplied as an arbitrary logical assumption rather than as a
construction, and print's Assumption 2 is precisely the claim that the
construction exists.
-/
public structure HarmReduction {Program Data : Type*} [Primcodable Data]
    (harms : Program → Data → Prop) where
  /-- Print's *HaltHarm()*, the program held fixed throughout the reduction. -/
  haltHarm : Program
  /-- The input `I` that print's data `(T, I)` carries. -/
  sourceInput : ℕ
  /-- Print's `D = (T, I)`, as a function of `T` alone. -/
  encode : Code → Data
  /-- The packaging is a construction, not an assumption. -/
  computable_encode : Computable encode
  /-- Print: *returns `TRUE` if and only if `T(I)` halts*. -/
  harms_iff_halts : ∀ source,
    harms haltHarm (encode source) ↔ (eval source sourceInput).Dom

/--
**Theorem 1. The harming problem is undecidable.**

Given print's composite construction, no total computable `Harm` decider exists.

The proof is print's: hold the program at *haltHarm*, let the data range over
encoded machines, and the decider becomes a decision procedure for halting.
-/
public theorem harming_undecidable {Program Data : Type*} [Primcodable Program]
    [Primcodable Data] {harms : Program → Data → Prop}
    (reduction : HarmReduction harms) :
    ¬ Nonempty (HarmDecider harms) := by
  rintro ⟨decider⟩
  let decision : Code → Bool := fun source =>
    decider.decide reduction.haltHarm (reduction.encode source)
  have decisionComputable : Computable decision :=
    decider.computable_decide.comp (Computable.const _) reduction.computable_encode
  have decisionCorrect : ∀ source,
      ((decision source : Prop) ↔ (eval source reduction.sourceInput).Dom) :=
    fun source =>
      (decider.correct reduction.haltHarm (reduction.encode source)).trans
        (reduction.harms_iff_halts source)
  have haltingComputable :
      ComputablePred fun source : Code => (eval source reduction.sourceInput).Dom :=
    ComputablePred.computable_iff.mpr ⟨decision, decisionComputable, by
      funext source
      exact propext (decisionCorrect source).symm⟩
  exact AISafetyAtlas.Computability.halting_problem reduction.sourceInput haltingComputable

/-! ## Print's own quantifier, and print's Assumption 2 as a statement

`harming_undecidable` above holds the input fixed and varies the machine,
because that is the shape of Mathlib's halting statement. Print varies both:
its data is the pair `(T, I)`. The three declarations below close that gap —
the halting problem at both arguments, the reduction stated over pairs, and
Theorem 1 from it — and the two after them state print's Assumption 2 rather
than only the constructibility it buys.
-/

/--
**The halting problem at both arguments**, which is the form print's `D = (T, I)`
ranges over.

Mathlib states it at a fixed input. The pair form follows at once and in the
easy direction: a decider for pairs restricts to a decider at input `0`, and
that one is Mathlib's.
-/
public theorem halting_problem_pair :
    ¬ ComputablePred fun p : Code × ℕ => (eval p.1 p.2).Dom := by
  intro hpair
  obtain ⟨f, hf, hfeq⟩ := ComputablePred.computable_iff.mp hpair
  refine AISafetyAtlas.Computability.halting_problem 0
    (ComputablePred.computable_iff.mpr
      ⟨fun c => f (c, 0),
        hf.comp (Computable.pair Computable.id (Computable.const 0)), ?_⟩)
  funext c
  exact congrFun hfeq (c, 0)

/--
**Print's reduction at print's own quantifier.** The data ranges over the pair
`(T, I)` rather than over `T` at one fixed `I`.

This is a *stronger* requirement on the construction than `HarmReduction` is:
the composite must reproduce halting at every input, not at one. Print's
Algorithm 3 meets it, which is what `Examples.Verification.Containment` shows.
-/
public structure HarmReductionPair {Program Data : Type*} [Primcodable Data]
    (harms : Program → Data → Prop) where
  /-- Print's *HaltHarm()*, the program held fixed throughout the reduction. -/
  haltHarm : Program
  /-- Print's `D = (T, I)`, as a function of the pair. -/
  encode : Code × ℕ → Data
  /-- The packaging is a construction, not an assumption. -/
  computable_encode : Computable encode
  /-- Print: *returns `TRUE` if and only if `T(I)` halts*, now at every `I`. -/
  harms_iff_halts : ∀ source input,
    harms haltHarm (encode (source, input)) ↔ (eval source input).Dom

/-- **The two source problems, reduced one to the other.** A reduction at
print's quantifier gives one at every fixed input, which is the claim the
coverage audit's Theorem 1 row used to make in prose and not in the tree. -/
public def HarmReductionPair.toHarmReduction {Program Data : Type*} [Primcodable Data]
    {harms : Program → Data → Prop} (reduction : HarmReductionPair harms) (input : ℕ) :
    HarmReduction harms where
  haltHarm := reduction.haltHarm
  sourceInput := input
  encode := fun source => reduction.encode (source, input)
  computable_encode :=
    reduction.computable_encode.comp (Computable.pair Computable.id (Computable.const input))
  harms_iff_halts := fun source => reduction.harms_iff_halts source input

/--
**Theorem 1 at print's own quantifier.** The harming problem is undecidable,
from a composite that reproduces halting at every machine *and* every input.

`harming_undecidable` is the stronger theorem, because its hypothesis is weaker;
this is the one whose hypothesis is print's sentence.
-/
public theorem harming_undecidable_pair {Program Data : Type*} [Primcodable Program]
    [Primcodable Data] {harms : Program → Data → Prop}
    (reduction : HarmReductionPair harms) :
    ¬ Nonempty (HarmDecider harms) :=
  harming_undecidable (reduction.toHarmReduction 0)

/--
**Print's Assumption 2**, as a condition on the composite rather than as the
constructibility it buys.

Print: *"`R` must be able to simulate a universal Turing machine and `D` includes
the set of inputs that can be executed by a universal Turing machine. In
addition, the language of `R` contains at least one explicit operation
*HarmHumans()* that harms humans and takes a finite time."*

Three clauses, in print's order.

* `simulates` is the first: run on the data that packages `(T, I)`, the
  composite computes what `T` computes on `I`. Print's *"takes a finite time"* is
  why this is an equality of partial functions and not an inclusion of domains —
  the appended operation neither diverges nor prunes.
* `covers` is the second: every machine-input pair the universal machine can be
  handed is packaged, and distinct pairs stay distinct, so the data type really
  does *include* them.
* `computable_encode` is the packaging being a construction.

*HarmHumans()* itself is not a clause of this structure, because it is
uninterpreted here exactly as it is in print; what the proof consumes from it is
the finiteness that `simulates` records. `Assumption2Harm` extends this
structure with print's last sentence as clauses, for an arbitrary effect relation.
-/
public structure Assumption2 (haltHarm : Code) (encode : Code × ℕ → ℕ) : Prop where
  /-- *"`R` must be able to simulate a universal Turing machine"*. -/
  simulates : ∀ source input, eval haltHarm (encode (source, input)) = eval source input
  /-- *"`D` includes the set of inputs that can be executed by a universal Turing
  machine"*. -/
  covers : Function.Injective encode
  /-- The packaging is computable. -/
  computable_encode : Computable encode

/--
**The effect relation print's Algorithm 3 has.** *"`R` run on `D` performs its
effect"*, which for a composite ending in an operation that *"takes a finite
time"* is exactly that the composite halts.
-/
@[expose] public def HaltsOn (program : Code) (data : ℕ) : Prop := (eval program data).Dom

/-- **Print's Assumption 2 delivers print's reduction.** The simulation clause
is the biconditional `harms_iff_halts` asks for, with nothing else added. -/
public def Assumption2.harmReductionPair {haltHarm : Code} {encode : Code × ℕ → ℕ}
    (assumption : Assumption2 haltHarm encode) : HarmReductionPair HaltsOn where
  haltHarm := haltHarm
  encode := encode
  computable_encode := assumption.computable_encode
  harms_iff_halts := fun source input => by
    simp only [HaltsOn, assumption.simulates source input]

/--
**Theorem 1 from print's Assumption 2 alone.**

Print's proof reads Assumption 2 and nothing else, and this is that proof: the
assumption gives the composite, the composite gives the reduction at every pair,
and the reduction gives the theorem.
-/
public theorem harming_undecidable_of_assumption2 {haltHarm : Code} {encode : Code × ℕ → ℕ}
    (assumption : Assumption2 haltHarm encode) :
    ¬ Nonempty (HarmDecider HaltsOn) :=
  harming_undecidable_pair assumption.harmReductionPair

/-! ## Print's *HarmHumans()*, as a clause

`Assumption2` leaves *HarmHumans()* out and fixes the effect relation to
`HaltsOn`. The declarations below state Assumption 2's last sentence too, for an
arbitrary effect relation `harms`: the language contains a program that harms
and takes a finite time, and print's *HaltHarm()* is that program run after the
universal machine. -/

/--
**Print's Assumption 2, all of it.** Alfonseca et al., JAIR 70 (2021), p. 71:
*"`R` must be able to simulate a universal Turing machine and `D` includes the
set of inputs that can be executed by a universal Turing machine. In addition,
the language of `R` contains at least one explicit operation *HarmHumans()* that
harms humans and takes a finite time."*

The first two sentences are `Assumption2` at the universal machine `universal`,
which is what print says can be simulated. The last is the two fields here, for
an uninterpreted effect relation `harms`: `harmHumans` *"takes a finite time"*
(`total`) and *"harms humans"* (`harmful`). The operation is explicit in the
language because `Code.comp` sequences it after any program, which is how
`haltHarm` is built.
-/
public structure Assumption2Harm (harms : Code → ℕ → Prop) (harmHumans universal : Code)
    (encode : Code × ℕ → ℕ) : Prop extends Assumption2 universal encode where
  /-- *HarmHumans()* *"takes a finite time"*. -/
  total : ∀ n, (eval harmHumans n).Dom
  /-- *HarmHumans()* *"harms humans"*. -/
  harmful : ∀ n, harms harmHumans n

/-- **Print's Algorithm 3**, *HaltHarm(T, I)*: *execute `T(I)`; execute
*HarmHumans()**. The universal machine runs the packaged `(T, I)`, then
*HarmHumans()* runs. -/
@[expose] public def haltHarmOf (harmHumans universal : Code) : Code :=
  Code.comp harmHumans universal

/-- **Print's observation, first half** (p. 70): *"*HarmHumans()* is executed
if and only if `T(I)` halts"*. Because *HarmHumans()* takes a finite time, the
composite runs to completion exactly when the simulated machine halts. -/
public theorem Assumption2Harm.haltHarm_dom_iff {harms : Code → ℕ → Prop}
    {harmHumans universal : Code} {encode : Code × ℕ → ℕ}
    (assumption : Assumption2Harm harms harmHumans universal encode) (source : Code)
    (input : ℕ) :
    (eval (haltHarmOf harmHumans universal) (encode (source, input))).Dom ↔
      (eval source input).Dom := by
  show (eval universal (encode (source, input)) >>= eval harmHumans).Dom ↔ _
  rw [assumption.simulates source input]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, assumption.total _⟩⟩

/--
**Print's Assumption 2 and observation deliver print's reduction, for any effect
relation.** The hypothesis `isolated` is the observation's second half (p. 70):
*"*HaltHarm()* harms humans if and only if *HarmHumans()* is executed, since the
execution of `T(I)` cannot harm humans"*, read as: the composite harms exactly
when it runs through *HarmHumans()*. It is required at the composite only.
-/
public def Assumption2Harm.harmReductionPair {harms : Code → ℕ → Prop}
    {harmHumans universal : Code} {encode : Code × ℕ → ℕ}
    (assumption : Assumption2Harm harms harmHumans universal encode)
    (isolated : ∀ d, harms (haltHarmOf harmHumans universal) d ↔
      (eval (haltHarmOf harmHumans universal) d).Dom) :
    HarmReductionPair harms where
  haltHarm := haltHarmOf harmHumans universal
  encode := encode
  computable_encode := assumption.computable_encode
  harms_iff_halts := fun source input =>
    (isolated _).trans (assumption.haltHarm_dom_iff source input)

/--
**Theorem 1 from print's Assumption 2 with *HarmHumans()*,** for an arbitrary
effect relation `harms` (Alfonseca et al., JAIR 70 (2021), p. 71): no total
computable `Harm` decider exists.
-/
public theorem harming_undecidable_of_assumption2Harm {harms : Code → ℕ → Prop}
    {harmHumans universal : Code} {encode : Code × ℕ → ℕ}
    (assumption : Assumption2Harm harms harmHumans universal encode)
    (isolated : ∀ d, harms (haltHarmOf harmHumans universal) d ↔
      (eval (haltHarmOf harmHumans universal) d).Dom) :
    ¬ Nonempty (HarmDecider harms) :=
  harming_undecidable_pair (assumption.harmReductionPair isolated)

/-- **Print's observation, first half, with "executed" read literally** (p. 70):
*"*HarmHumans()* is executed if and only if `T(I)` halts"*. In the composite
`haltHarmOf harmHumans universal`, the second step runs on the output of the
first, so *HarmHumans()* is executed on the packaged `(T, I)` exactly when the
universal machine returns there; that is `T(I)` halting.
`Assumption2Harm.haltHarm_dom_iff` is the same fact for the whole composite
completing, which under *HarmHumans()*'s totality says the same. -/
public theorem Assumption2Harm.harmHumans_executed_iff {harms : Code → ℕ → Prop}
    {harmHumans universal : Code} {encode : Code × ℕ → ℕ}
    (assumption : Assumption2Harm harms harmHumans universal encode) (source : Code)
    (input : ℕ) :
    (eval universal (encode (source, input))).Dom ↔ (eval source input).Dom := by
  rw [assumption.simulates source input]

/-! ## Print's isolation premise, and the biconditional derived from it

`Assumption2Harm.harmReductionPair` takes the observation's second half as a
hypothesis at the composite. Print *derives* it: *"*HaltHarm()* harms humans if
and only if *HarmHumans()* is executed, since the execution of `T(I)` cannot harm
humans, as a Turing machine is isolated from the external world"*. The structure
below states the two premises of that sentence for an arbitrary effect relation,
and the theorems after it derive the biconditional and print's reduction. -/

/--
**Print's effect semantics for Algorithm 3** (Alfonseca et al., JAIR 70 (2021),
p. 70), as premises on an effect relation `harms`.

* `isolated`: *"the execution of `T(I)` cannot harm humans, as a Turing machine
  is isolated from the external world"*: the universal machine, run on any
  packaged `(T, I)`, does not harm.
* `seq`: the composite *execute `T(I)`; execute *HarmHumans()** harms exactly
  when its first step harms or the first step returns and *HarmHumans()* harms
  when run after it.

It is stated at print's one composite rather than for every sequencing of codes,
since that is all print's sentence speaks about. It cannot be met by `HaltsOn`,
under which the universal machine harms wherever it halts; the example module
gives a relation meeting it.
-/
public structure SequentialHarm (harms : Code → ℕ → Prop) (harmHumans universal : Code)
    (encode : Code × ℕ → ℕ) : Prop where
  /-- *"The execution of `T(I)` cannot harm humans"*. -/
  isolated : ∀ source input, ¬ harms universal (encode (source, input))
  /-- The composite harms iff its first step harms, or the first step returns and
  *HarmHumans()* harms on what it returned. -/
  seq : ∀ d, harms (haltHarmOf harmHumans universal) d ↔
    harms universal d ∨ ∃ y ∈ eval universal d, harms harmHumans y

/-- **Print's observation, second half, derived** (p. 70): *"*HaltHarm()* harms
humans if and only if *HarmHumans()* is executed"*, from isolation, the
sequencing premise, and *HarmHumans()* harming (`Assumption2Harm.harmful`). -/
public theorem SequentialHarm.harms_iff_executed {harms : Code → ℕ → Prop}
    {harmHumans universal : Code} {encode : Code × ℕ → ℕ}
    (sem : SequentialHarm harms harmHumans universal encode)
    (assumption : Assumption2Harm harms harmHumans universal encode) (source : Code)
    (input : ℕ) :
    harms (haltHarmOf harmHumans universal) (encode (source, input)) ↔
      (eval universal (encode (source, input))).Dom := by
  rw [sem.seq, or_iff_right (sem.isolated source input)]
  exact ⟨fun ⟨y, hy, _⟩ => Part.dom_iff_mem.mpr ⟨y, hy⟩,
    fun h => ⟨_, Part.get_mem h, assumption.harmful _⟩⟩

/-- **Print's line *"returns `TRUE` if and only if `T(I)` halts"*, derived from
print's premises** rather than assumed: isolation and sequencing give the harm
biconditional, and Assumption 2's simulation gives halting. -/
public theorem SequentialHarm.harms_haltHarmOf_iff_halts {harms : Code → ℕ → Prop}
    {harmHumans universal : Code} {encode : Code × ℕ → ℕ}
    (sem : SequentialHarm harms harmHumans universal encode)
    (assumption : Assumption2Harm harms harmHumans universal encode) (source : Code)
    (input : ℕ) :
    harms (haltHarmOf harmHumans universal) (encode (source, input)) ↔
      (eval source input).Dom :=
  (sem.harms_iff_executed assumption source input).trans
    (assumption.harmHumans_executed_iff source input)

/-- **Print's reduction from print's premises**: Assumption 2 with *HarmHumans()*
and the isolation semantics give a `HarmReductionPair`, which
`harming_undecidable_pair` turns into Theorem 1. -/
public def SequentialHarm.toHarmReductionPair {harms : Code → ℕ → Prop}
    {harmHumans universal : Code} {encode : Code × ℕ → ℕ}
    (sem : SequentialHarm harms harmHumans universal encode)
    (assumption : Assumption2Harm harms harmHumans universal encode) :
    HarmReductionPair harms where
  haltHarm := haltHarmOf harmHumans universal
  encode := encode
  computable_encode := assumption.computable_encode
  harms_iff_halts := sem.harms_haltHarmOf_iff_halts assumption

end AISafetyAtlas.Verification.Containment
