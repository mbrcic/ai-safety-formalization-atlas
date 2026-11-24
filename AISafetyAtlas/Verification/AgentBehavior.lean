module

public import AISafetyAtlas.Verification

/-!
# Downstream consumer of `Verification.rice`

## Statement intent

- **System object:** an *encoded agent* is a Mathlib program code whose
  operational meaning is a partial input/output map `ℕ →. ℕ`.
- **Safety specification:** a set of acceptable partial I/O behaviors
  (`SafetySpec` = `BehavioralProperty`).
- **Decider:** a total computable `BehavioralSafetyVerifier` that is sound and
  complete for whether an agent satisfies the specification.
- **Assumption:** the specification is nontrivial — some representable agent is
  safe and some is not.
- **Conclusion:** no such total verifier exists.
- **Statement source:** Melo, Máximo, Soma and Castro,
  [arXiv:2408.08995v1](https://arxiv.org/abs/2408.08995) (also Sci. Rep. 2025;
  catalog `atlas-ref-melo-2024`, row `LAND-VERIF-AGENTBEHAVIOR-001`).
- **Proof route:** reduces through `AISafetyAtlas.Verification.rice`
  (semantic-to-code bridge over Mathlib Rice), not by re-proving Rice.
  Classical statement: H. G. Rice, *Classes of Recursively Enumerable Sets and
  Their Decision Problems*, Trans. AMS 74(2):358–366, 1953 (survey BY-012 /
  `survey-ref-037`).

## Which work plays which role

**Corrected 2026-09-11, and the two used to be the other way round.** This
header named Rice as the *source* and filed Melo et al. under *"related
literature"*. Reading Melo et al. settles it: **they state the claim this
module's theorem renders**, and Rice is the route to it. Their abstract's first
sentence is *"The inner alignment problem, which asserts whether an arbitrary
artificial intelligence (AI) model satisfices a non-trivial alignment function
of its outputs given its inputs, is undecidable"*, and their *Formal Proof*
section supplies the four things this module carries: the objects are **partial**
functions (their own words, which matters because their title is *Machines that
Halt*), the property is extensional, non-triviality comes with **both**
witnesses, and "decides" means total, computable and correct in both directions.

Print's judge itself is stated at the end of this file: `Judge`, `JudgeNontrivial`,
the property `judgeSpec` it induces, and `judgeSpec_nontrivial`, print's
*"the non-triviality of the judge function guarantees the non-triviality of the
property"*, so `no_behavioral_safety_verifier` can be fired at a judge.

Print gives two routes — *"could simply be reduced to a restatement of Rice's
Theorem"*, and an explicit Halting-Problem reduction. **The theorem takes the
first.** The second is stated as the reduction itself,
`halting_reduces_to_spec`: a computable map from codes to codes reducing halting
at a fixed input to the specification, or to its complement when the
nowhere-defined behaviour satisfies it. Print's literal `M′` is stated where it
exists (`halting_reduces_to_spec_of_none_not_mem`, and at the judge's property
`halting_reduces_to_judgeSpec`), and refuted under the other reading of the
judge's property (`not_exists_halting_reduction_judgeSpecOutputs`). Which reading
print means awaits the authors' ruling.

Graded in section 24 of `docs/provenance/source-coverage-audit.md`: 5 Yes,
0 Partial, 5 No, 1 Beyond. The atlas formalizes their undecidability claim and
**not** their second half — the enumerable set of architecturally aligned models,
the finite-input decidable case, or the proposed halting constraint on the judge.
Basics and coverage estimate: `docs/guide/related-literature.md`.

Related but distinct: Alfonseca et al., *Superintelligence cannot be contained*
(JAIR 2021; `survey-ref-056`).

Registry BY-012 (statement layer). Coverage:
`docs/status/sources/brcic-yampolskiy-2023.md`. Review:
`docs/interpretation-reviews/review-by-012-agentbehavior.md`.

CT-4 / R6-8 consumer of `Verification.rice`. Does not claim that every
practical safety property is extensional I/O behavior, that a particular
system is encoded by `eval`, or that incomplete verifiers are impossible.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Verification.AgentBehavior

/-- An encoded agent: a program code with partial recursive I/O semantics. -/
public abbrev Agent := Code

/-- A behavioral safety specification on partial input/output maps. -/
public abbrev SafetySpec := AISafetyAtlas.Verification.BehavioralProperty

/-- Agent `agent` realizes a behavior in the safety specification. -/
public def Satisfies (spec : SafetySpec) (agent : Agent) : Prop :=
  AISafetyAtlas.Verification.Holds spec agent

/-- The specification accepts at least one representable agent and rejects another. -/
public abbrev SpecNontrivial (spec : SafetySpec) : Prop :=
  AISafetyAtlas.Verification.Nontrivial spec

/--
A total computable procedure that correctly classifies every encoded agent
against a fixed behavioral safety specification.
-/
public structure BehavioralSafetyVerifier (spec : SafetySpec) where
  decide : Agent → Bool
  computable_decide : Computable decide
  correct : ∀ agent, (decide agent : Prop) ↔ Satisfies spec agent

/--
No total computable behavioral safety verifier exists for a nontrivial I/O
safety specification on encoded agents.

Machine-checked reduction to `AISafetyAtlas.Verification.rice`. Same
agent/program + nontrivial I/O-judge pattern as Melo et al.
(arXiv:2408.08995); see the module docstring for scope.
-/
public theorem no_behavioral_safety_verifier
    (spec : SafetySpec) (nontrivial : SpecNontrivial spec) :
    ¬ Nonempty (BehavioralSafetyVerifier spec) := by
  rintro ⟨verifier⟩
  have hasVerifier : AISafetyAtlas.Verification.HasVerifier spec := by
    refine ComputablePred.computable_iff.mpr
      ⟨verifier.decide, verifier.computable_decide, ?_⟩
    funext agent
    exact propext (verifier.correct agent).symm
  exact AISafetyAtlas.Verification.rice spec nontrivial hasVerifier

/-! ## Print's second route: the halting reduction

Melo et al. (arXiv:2408.08995v1, Formal Proof, p. 3) also argue through the
halting problem: from `M` and an input `i` they build `M′`, which simulates `M`
on `i` and then computes a function with or without `P`, so that a decider for
`P` decides whether `M` halts on `i`. `halting_reduces_to_spec` is that
reduction, as a computable many-one map. When the nowhere-defined function
lacks `P` it is print's literal `M′` (`halting_reduces_to_spec_of_none_not_mem`).
When the nowhere-defined function has `P`, the map below reduces halting to the
*complement* of `P` instead, and print's literal `M′` need not exist: for a
co-r.e. `P` it does not (`not_exists_halting_reduction_of_compl_re`, it would make
non-halting recursively enumerable). Which case print's judge-defined `P` falls in
depends on the reading of the judge; both are stated at the end of this file, and
the choice awaits the authors' ruling. Either way a decider for `P` decides
halting at `i`. -/

/-- `M′` is `M` on `i` followed by `c`: the curried code `k` runs `M` on `i`,
discards the result, and runs `c` on its own input. -/
private theorem exists_gate (c : Code) (i : ℕ) : ∃ k : Code, ∀ (M : Code) (x : ℕ),
    eval (Code.curry k (Encodable.encode M)) x = (eval M i).bind fun _ => eval c x := by
  have hpart : Partrec fun n : ℕ =>
      (eval (Denumerable.ofNat Code (Nat.unpair n).1) i).bind
        fun _ => eval c (Nat.unpair n).2 :=
    Partrec.bind
      (eval_part.comp ((Computable.ofNat Code).comp (Primrec.fst.comp Primrec.unpair).to_comp)
        (Computable.const i))
      (eval_part.comp (Computable.const c)
        ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst)).to₂
  obtain ⟨k, hk⟩ := exists_code.mp (Partrec.nat_iff.mp hpart)
  refine ⟨k, fun M x => ?_⟩
  rw [eval_curry, hk]
  simp [Nat.unpair_pair, Denumerable.ofNat_encode]

/-- Where `M` halts on `i`, the gated behaviour is `c`'s. -/
private theorem eval_gate_of_dom {M c k : Code} {i : ℕ}
    (hk : ∀ (M : Code) (x : ℕ),
      eval (Code.curry k (Encodable.encode M)) x = (eval M i).bind fun _ => eval c x)
    (h : (eval M i).Dom) : eval (Code.curry k (Encodable.encode M)) = eval c := by
  funext x
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp h
  rw [hk, Part.eq_some_iff.mpr hy, Part.bind_some]

/-- Where `M` does not halt on `i`, the gated behaviour is nowhere defined. -/
private theorem eval_gate_of_not_dom {M c k : Code} {i : ℕ}
    (hk : ∀ (M : Code) (x : ℕ),
      eval (Code.curry k (Encodable.encode M)) x = (eval M i).bind fun _ => eval c x)
    (h : ¬ (eval M i).Dom) :
    eval (Code.curry k (Encodable.encode M)) = fun _ => Part.none := by
  funext x
  rw [hk, Part.eq_none_iff'.mpr h, Part.bind_none]

/--
**Print's literal `M′`, where the nowhere-defined behaviour lacks the property**
(Melo et al., arXiv:2408.08995v1, Formal Proof, p. 3: *"If `M` halts on `i`, then
`M′` computes a partial function with property `P`. If `M` does not halt on `i`,
then `M′` computes a partial function without property `P`"*).

A computable `M ↦ M′` with `M′ ∈ P` exactly when `M` halts on `i`, for every
non-trivial specification that excludes the nowhere-defined function. Under the
library's reading of print's judge-defined property (`judgeSpec`, every input
receives an accepted output) that exclusion always holds
(`halting_reduces_to_judgeSpec`). Under the other reading it fails, and print's
literal `M′` does not exist there (`not_exists_halting_reduction_judgeSpecOutputs`).
-/
public theorem halting_reduces_to_spec_of_none_not_mem (spec : SafetySpec)
    (nontrivial : SpecNontrivial spec) (hnone : (fun _ => Part.none : ℕ →. ℕ) ∉ spec)
    (i : ℕ) :
    ∃ f : Agent → Agent, Computable f ∧ ∀ M, Satisfies spec (f M) ↔ (eval M i).Dom := by
  obtain ⟨⟨accepted, hacc⟩, -⟩ := nontrivial
  obtain ⟨k, hk⟩ := exists_gate accepted i
  refine ⟨fun M => Code.curry k (Encodable.encode M),
    (primrec₂_curry.comp (Primrec.const k) Primrec.encode).to_comp, fun M => ?_⟩
  simp only [Satisfies, AISafetyAtlas.Verification.Holds]
  by_cases h : (eval M i).Dom
  · rw [eval_gate_of_dom hk h]; exact iff_of_true hacc h
  · rw [eval_gate_of_not_dom hk h]; exact iff_of_false hnone h

/--
**Print's halting reduction** (Melo et al., arXiv:2408.08995v1, Formal Proof,
p. 3: *"We construct a new Turing machine `M′` … We can now use `M_P` to decide
whether `M′` computes a partial function with property `P`. If `M_P` accepts, then
`M` halts on `i`"*), as a computable many-one reduction from halting at `i` to a
non-trivial specification or to its complement.

The map is `M ↦ M′`, where `M′` runs `M` on `i` and then an agent inside (or
outside) the specification. If the nowhere-defined behaviour is outside the
specification, `M′` satisfies it exactly when `M` halts on `i`, which is print's
construction. Otherwise `M′` fails it exactly when `M` halts on `i`, the
complement form (see the section header for the status of print's literal `M′`
in that case). Composing a
`BehavioralSafetyVerifier` with the map, negated in the second case, decides
halting at `i`, against `AISafetyAtlas.Computability.halting_problem`.
-/
public theorem halting_reduces_to_spec (spec : SafetySpec) (nontrivial : SpecNontrivial spec)
    (i : ℕ) :
    ∃ f : Agent → Agent, Computable f ∧
      ((∀ M, Satisfies spec (f M) ↔ (eval M i).Dom) ∨
        (∀ M, ¬ Satisfies spec (f M) ↔ (eval M i).Dom)) := by
  classical
  obtain ⟨⟨accepted, hacc⟩, ⟨rejected, hrej⟩⟩ := nontrivial
  have hcomp : ∀ k : Code, Computable fun M : Code => Code.curry k (Encodable.encode M) :=
    fun k => (primrec₂_curry.comp (Primrec.const k) Primrec.encode).to_comp
  by_cases hnone : (fun _ => Part.none : ℕ →. ℕ) ∈ spec
  · obtain ⟨k, hk⟩ := exists_gate rejected i
    refine ⟨fun M => Code.curry k (Encodable.encode M), hcomp k, Or.inr fun M => ?_⟩
    simp only [Satisfies, AISafetyAtlas.Verification.Holds]
    by_cases h : (eval M i).Dom
    · rw [eval_gate_of_dom hk h]; exact iff_of_true hrej h
    · rw [eval_gate_of_not_dom hk h]; exact iff_of_false (not_not.mpr hnone) h
  · obtain ⟨f, hf, hred⟩ :=
      halting_reduces_to_spec_of_none_not_mem spec ⟨⟨accepted, hacc⟩, ⟨rejected, hrej⟩⟩ hnone i
    exact ⟨f, hf, Or.inl hred⟩

/-! ## Print's judge, and the property it defines

Melo et al. (arXiv:2408.08995v1, p. 2) give the property through a judge
`J_v(i, o)` that returns *True* (byte 1) or *False* (byte 0), and require it
non-trivial; their Formal Proof (p. 3) says the non-triviality of the judge
*"guarantees the non-triviality of the property"*. `SafetySpec` above is any set
of partial behaviors; the three declarations below are the judge, its
non-triviality, and the property it induces, and `judgeSpec_nontrivial` is
print's sentence. -/

/-- **Print's judge `J_v(i, o)`** (Melo et al., p. 2): input and output bytes,
coded as naturals, to *True*/*False*. Print's standing assumption that the judge
is computable (p. 1) is a hypothesis where it is used, not part of the type. -/
public abbrev Judge := ℕ → ℕ → Bool

/-- **Print's non-triviality of the judge** (Melo et al., p. 2): *"there is at
least one negative input `(i⁻, o⁻)` that returns 0 and at least one output `o⁺`
for every input `i` which the judge returns 1"*. -/
@[expose] public def JudgeNontrivial (judge : Judge) : Prop :=
  (∃ i o, judge i o = false) ∧ ∀ i, ∃ o, judge i o = true

/-- **The property defined by the judge** (Melo et al., p. 3, *"the property as
defined by the acceptance of the output given the input by a judge function"*):
the behavior produces, on every input, an output the judge accepts.

Print's verifier (p. 2) returns *True* when *"the model is aligned for every
input `i` and output `M(i) = o`"*. This takes the reading in which every input
must receive an accepted output, so a behavior that diverges somewhere is not
aligned. The other reading (every output produced is accepted) accepts the
nowhere-defined machine, and then print's `o⁺` clause, the judge's computability
and print's *"a TM can be built to always output the dummy positive values"*
all carry no weight; here each of them is used. Extensionality (print's
preceding sentence) holds by construction, since this is a set of partial
functions. -/
@[expose] public def judgeSpec (judge : Judge) : SafetySpec :=
  {behavior | ∀ i, ∃ o ∈ behavior i, judge i o = true}

/--
**The non-triviality of the judge guarantees the non-triviality of the
property** (Melo et al., arXiv:2408.08995v1, Formal Proof, p. 3).

Print's two machines: one that *"always output[s] the dummy positive values"*
(here the code of `i ↦ Nat.rfind (judge i ·)`, total because every input has an
`o⁺`, and partial recursive because the judge is computable), and one that
*"output[s] at least one dummy negative value"* (the constant code at `o⁻`,
rejected at `i⁻`).
-/
public theorem judgeSpec_nontrivial (judge : Judge) (computable : Computable₂ judge)
    (nontrivial : JudgeNontrivial judge) : SpecNontrivial (judgeSpec judge) := by
  obtain ⟨⟨iNeg, oNeg, rejects⟩, positive⟩ := nontrivial
  refine ⟨?_, ⟨Code.const oNeg, ?_⟩⟩
  · have searchPartrec : Partrec fun i => Nat.rfind fun o => (judge i o : Part Bool) :=
      Partrec.rfind computable.partrec₂
    obtain ⟨code, hcode⟩ := exists_code.mp (Partrec.nat_iff.mp searchPartrec)
    refine ⟨code, fun i => ?_⟩
    have hdom : (Nat.rfind fun o => (judge i o : Part Bool)).Dom := by
      obtain ⟨o, ho⟩ := positive i
      exact Nat.rfind_dom'.mpr ⟨o, by simp [ho], fun _ => trivial⟩
    refine ⟨(Nat.rfind fun o => (judge i o : Part Bool)).get hdom, ?_, ?_⟩
    · rw [hcode]
      exact Part.get_mem hdom
    · simpa using Nat.rfind_spec (Part.get_mem hdom)
  · intro accepted
    obtain ⟨o, ho, hjudge⟩ := accepted iNeg
    simp only [eval_const, Part.mem_some_iff] at ho
    subst ho
    simp [rejects] at hjudge

/-! ## Print's literal `M′` under the two readings of the judge's property

The `judgeSpec` docstring names two readings of print's judge-defined `P`. Which
one print means is the authors' call; the coverage audit records the question.
At `judgeSpec` (every input receives an accepted output) the nowhere-defined
function lacks `P`, and print's literal `M′` exists:
`halting_reduces_to_judgeSpec`. At `judgeSpecOutputs` (every output produced is
accepted) the nowhere-defined function has `P`, `P` is co-r.e., and print's literal
`M′` does not exist: `not_exists_halting_reduction_judgeSpecOutputs`. -/

/-- The nowhere-defined behaviour produces no output at input `0`, so no judge's
`judgeSpec` contains it. -/
public theorem none_not_mem_judgeSpec (judge : Judge) :
    (fun _ => Part.none : ℕ →. ℕ) ∉ judgeSpec judge := by
  intro h
  obtain ⟨o, ho, -⟩ := h 0
  exact Part.notMem_none o ho

/--
**Print's literal `M′` at the library's reading of the judge** (Melo et al.,
arXiv:2408.08995v1, Formal Proof, p. 3): for a computable non-trivial judge, a
computable `M ↦ M′` such that `M′` computes a partial function with the property
`judgeSpec judge` exactly when `M` halts on `i`.
-/
public theorem halting_reduces_to_judgeSpec (judge : Judge) (computable : Computable₂ judge)
    (nontrivial : JudgeNontrivial judge) (i : ℕ) :
    ∃ f : Agent → Agent, Computable f ∧
      ∀ M, Satisfies (judgeSpec judge) (f M) ↔ (eval M i).Dom :=
  halting_reduces_to_spec_of_none_not_mem _ (judgeSpec_nontrivial judge computable nontrivial)
    (none_not_mem_judgeSpec judge) i

/--
**No literal `M′` for a co-r.e. property.** If failing the specification is
recursively enumerable, no computable `M ↦ M′` has `M′` satisfying it exactly when
`M` halts on `i`: composing would make non-halting at `i` recursively enumerable,
against Mathlib's `ComputablePred.halting_problem_not_re`. No non-triviality or
judge is assumed.
-/
public theorem not_exists_halting_reduction_of_compl_re (spec : SafetySpec) (i : ℕ)
    (hco : REPred fun M : Agent => ¬ Satisfies spec M) :
    ¬ ∃ f : Agent → Agent, Computable f ∧ ∀ M, Satisfies spec (f M) ↔ (eval M i).Dom := by
  rintro ⟨f, hf, hred⟩
  have hcomp : REPred fun M : Agent => ¬ Satisfies spec (f M) := hco.comp hf
  exact ComputablePred.halting_problem_not_re i (hcomp.of_eq fun M => not_congr (hred M))

/-- **The other reading of print's judge-defined property** (the alternative named
in the `judgeSpec` docstring): every output the behaviour produces is accepted by
the judge. The nowhere-defined behaviour has it. -/
@[expose] public def judgeSpecOutputs (judge : Judge) : SafetySpec :=
  {behavior | ∀ i, ∀ o ∈ behavior i, judge i o = true}

/-- The nowhere-defined behaviour has every judge's `judgeSpecOutputs`. -/
public theorem none_mem_judgeSpecOutputs (judge : Judge) :
    (fun _ => Part.none : ℕ →. ℕ) ∈ judgeSpecOutputs judge :=
  fun _ o ho => absurd ho (Part.notMem_none o)

/-- For a computable judge, failing `judgeSpecOutputs` is recursively enumerable:
search the input, the step bound, and the output together, and stop at a produced
output the judge rejects. -/
public theorem judgeSpecOutputs_compl_re (judge : Judge) (computable : Computable₂ judge) :
    REPred fun M : Agent => ¬ Satisfies (judgeSpecOutputs judge) M := by
  let test : Code → ℕ → Bool := fun c m =>
    Option.casesOn (evaln (Nat.unpair m).2 c (Nat.unpair m).1) false
      fun o => !judge (Nat.unpair m).1 o
  have htest : Computable₂ test := by
    have hev : Computable fun p : Code × ℕ => evaln (Nat.unpair p.2).2 p.1 (Nat.unpair p.2).1 :=
      (primrec_evaln.comp (((Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).pair
        Primrec.fst).pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))).to_comp
    exact Computable.option_casesOn hev (Computable.const false)
      (Primrec.not.to_comp.comp (computable.comp
        (Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst)))
        Computable.snd)).to₂
  have hpart : Partrec fun c => Nat.rfind fun m => Part.some (test c m) :=
    Partrec.rfind (p := fun c m => Part.some (test c m)) htest.partrec₂
  refine (Partrec.dom_re hpart).of_eq fun c => ?_
  have hdom : (Nat.rfind fun m => Part.some (test c m)).Dom ↔ ∃ m, test c m = true := by
    constructor
    · intro h
      exact ⟨_, by simpa using Nat.rfind_spec (Part.get_mem h)⟩
    · rintro ⟨m, hm⟩
      exact Nat.rfind_dom'.mpr ⟨m, by simp [hm], fun _ => trivial⟩
  rw [hdom]
  simp only [Satisfies, AISafetyAtlas.Verification.Holds, judgeSpecOutputs]
  constructor
  · rintro ⟨m, hm⟩ hall
    simp only [test] at hm
    cases he : evaln (Nat.unpair m).2 c (Nat.unpair m).1 with
    | none => rw [he] at hm; exact Bool.false_ne_true hm
    | some o =>
      rw [he] at hm
      have := hall (Nat.unpair m).1 o (evaln_sound he)
      simp [this] at hm
  · intro hnot
    have hnot' : ¬ ∀ i o, o ∈ eval c i → judge i o = true := hnot
    push Not at hnot'
    obtain ⟨i, o, ho, hj⟩ := hnot'
    obtain ⟨k, hk⟩ := evaln_complete.mp ho
    refine ⟨Nat.pair i k, ?_⟩
    simp only [test, Nat.unpair_pair]
    rw [show evaln k c i = some o from hk]
    simp [hj]

/--
**Print's literal `M′` does not exist at the other reading** (Melo et al.,
arXiv:2408.08995v1, Formal Proof, p. 3, read with `judgeSpecOutputs`): for a
computable judge, no computable `M ↦ M′` has `M′` computing a function with the
property exactly when `M` halts on `i`.
-/
public theorem not_exists_halting_reduction_judgeSpecOutputs (judge : Judge)
    (computable : Computable₂ judge) (i : ℕ) :
    ¬ ∃ f : Agent → Agent, Computable f ∧
      ∀ M, Satisfies (judgeSpecOutputs judge) (f M) ↔ (eval M i).Dom :=
  not_exists_halting_reduction_of_compl_re _ i (judgeSpecOutputs_compl_re judge computable)

end AISafetyAtlas.Verification.AgentBehavior
