import AISafetyAtlas.Verification.AgentBehavior

/-!
# Melo et al.'s halting-reduction machine `M′` as printed does not exist; the repaired one does

Gabriel A. Melo, Marcos R. O. A. Máximo, Nei Y. Soma and Paulo A. L. Castro, *On the
Undecidability of Artificial Intelligence Alignment: Machines that Halt*,
arXiv:2408.08995v1 (2024), §Formal Proof, p. 3 (PDF p. 3; audit row S24-R05, the
"agent" row; registry BY-012, catalogued through the Brcic–Yampolskiy survey):

    Let $M$ be a Turing machine and $i$ be an input to $M$. We want to decide
    whether $M$ halts on $i$. We construct a new Turing machine $M'$ as follows:
    - On input $i$, $M'$ simulates $M$ on $i$.
    - If $M$ halts on $i$, then $M'$ computes a partial function with property $P$.
    - If $M$ does not halt on $i$, then $M'$ computes a partial function without
      property $P$.
    We can now use $M_P$ to decide whether $M'$ computes a partial function with
    property $P$. If $M_P$ accepts, then $M$ halts on $i$. If $M_P$ rejects, then
    $M$ does not halt on $i$.

(Transcribed from the page image in
`docs/provenance/printed-statements/melo-2024-undecidability-alignment.yaml`,
entry `melo-formal-proof-agent`.) `P` is a non-trivial property of the partial
function a machine computes (the yaml's `melo-formal-proof-property`).

Read literally, the construction does not exist for every such `P`. Print's `M′` is a
computable many-one reduction of halting at `i` to `P` itself, with no negation: print
reads `M_P`'s answer directly. Such a reduction makes "`M` does not halt on `i`" the
preimage of "not `P`". Take `P` = "every output produced is `0`" (`onlyZero`). It is
non-trivial (the constant-`0` program has it, the constant-`1` program does not), and
"not `P`" is recursively enumerable: search, dovetailing over inputs and step bounds,
for an input on which the program outputs a non-zero value. So non-halting at `i`
would be r.e., which Mathlib's `ComputablePred.halting_problem_not_re` (via the
library's `AISafetyAtlas.Computability.nonhalting_not_re`) forbids. The obstruction is
any `P` containing the nowhere-defined function whose complement is r.e.; print's
second bullet asks `M′` to land outside `P` exactly when it diverges, but a machine
that never halts computes the nowhere-defined function, which is inside `P`.

**Modelling choice: the program model.** Print says "Turing machine" and fixes no
formal model. The library, and this file, use Mathlib's `Nat.Partrec.Code`, a
Turing-complete programming language for the partial recursive functions, with `eval`
as the partial function a code computes and `Computable` as "a Turing machine
computes the map". The argument transfers to any model with an effective
step-bounded simulator (Turing machines encoded as numbers included); that transfer
is not proved here.

**Modelling choice: the map `M ↦ M′` must be computable.** Print builds `M_H` from
`M_P` and `M′` as a Turing machine, so `M′` must be produced from `M` effectively.
Without that requirement the statement is trivially true (choose, for each `M`,
some program inside or outside `P` according to whether `M` halts). `LiteralPrint`
quantifies over every computable map, not only print's simulate-then-run
construction, so the refutation covers any way of building `M′`. For the same
reason it does not matter that print uses one letter `i` both for `M′`'s input and
for the fixed input of `M`.

**Modelling choice: which `P`.** `LiteralPrint` ranges over every non-trivial
behavioural property in the library's form (`SafetySpec`, `SpecNontrivial`). Print's
Formal Proof obtains `P` from a judge, "the property as defined by the acceptance of
the output given the input by a judge function". The witness is such a property under
the partial-correctness reading of the judge (every output produced is accepted),
for the computable non-trivial judge `zeroJudge` that accepts exactly output `0`
(`onlyZero_eq_judge`, `zeroJudge_computable`, `zeroJudge_nontrivial`). The library's
`judgeSpec` takes the other reading (every input receives an accepted output), under
which the nowhere-defined function is never in the property
(`none_not_mem_judgeSpec`) and this witness is not available. This file neither
proves nor refutes print's literal `M′` for `judgeSpec` properties.

Why the repair is the necessary one and not a different theorem: it keeps print's
construction and changes only the read-out. When the nowhere-defined function has
`P`, `M′` is built to fail `P` exactly when `M` halts on `i`, and `M_H` negates
`M_P`'s answer. A decider for `P` still decides halting at `i`, which is all print's
proof uses. The library states this as `halting_reduces_to_spec`.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/melo-mprime-literal.lean`.
Grading context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired
slips).
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code
open AISafetyAtlas.Verification.AgentBehavior

namespace MeloMPrimeLiteral

/-- Print's construction exactly as printed: for every non-trivial behavioural
property `P` and every input `i`, a computable map `M ↦ M′` such that `M′` computes a
partial function with `P` exactly when `M` halts on `i`. -/
def LiteralPrint : Prop :=
  ∀ P : SafetySpec, SpecNontrivial P → ∀ i : ℕ,
    ∃ f : Agent → Agent, Computable f ∧ ∀ M, eval (f M) ∈ P ↔ (eval M i).Dom

/-- The witness: every output produced is `0`. The nowhere-defined function has it. -/
def onlyZero : SafetySpec := {g | ∀ n, ∀ v ∈ g n, v = 0}

/-- It is non-trivial: the constant-`0` program has it, the constant-`1` program does
not. -/
theorem onlyZero_nontrivial : SpecNontrivial onlyZero := by
  refine ⟨⟨Code.const 0, ?_⟩, ⟨Code.const 1, fun h => ?_⟩⟩
  · show ∀ n, ∀ v ∈ eval (Code.const 0) n, v = 0
    intro n v hv
    simp only [eval_const, Part.mem_some_iff] at hv
    exact hv
  · exact absurd (h 0 1 (by simp [eval_const])) one_ne_zero

/-- Step-bounded search for a non-zero output of `c`: at `k`, run `c` on input
`k.unpair.1` for `k.unpair.2` steps and keep a non-zero result. -/
private def search (c : Code) (k : ℕ) : Option ℕ :=
  (evaln k.unpair.2 c k.unpair.1).bind fun v => if v = 0 then none else some v

private theorem search_primrec : Primrec₂ search := by
  have h : Primrec fun p : Code × ℕ => evaln p.2.unpair.2 p.1 p.2.unpair.1 :=
    primrec_evaln.comp (Primrec.pair
      (Primrec.pair (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst)
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
  exact Primrec.option_bind h
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const none)
      (Primrec.option_some.comp Primrec.snd))

/-- The search halts exactly when `c` outputs a non-zero value somewhere, i.e. when
`c` lacks `onlyZero`. -/
private theorem search_dom (c : Code) :
    (Nat.rfindOpt (search c)).Dom ↔ eval c ∉ onlyZero := by
  rw [Nat.rfindOpt_dom]
  simp only [onlyZero, Set.mem_ofPred_eq, not_forall]
  constructor
  · rintro ⟨k, a, h⟩
    simp only [search, Option.mem_def, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h2⟩ := h
    split_ifs at h2 with h0
    exact ⟨k.unpair.1, v, evaln_sound hv, h0⟩
  · rintro ⟨n, v, hv, h0⟩
    obtain ⟨s, hs⟩ := evaln_complete.mp hv
    refine ⟨Nat.pair n s, v, ?_⟩
    simp only [search, Nat.unpair_pair, Option.mem_def, Option.bind_eq_some_iff]
    exact ⟨v, hs, by simp [h0]⟩

/-- **Print's `M′` does not exist for `onlyZero`, at any input `i`.** Such a map
would make non-halting at `i` recursively enumerable. -/
theorem literal_false_at (i : ℕ) :
    ¬ ∃ f : Agent → Agent, Computable f ∧ ∀ M, eval (f M) ∈ onlyZero ↔ (eval M i).Dom := by
  rintro ⟨f, hf, hiff⟩
  have hre : REPred fun M : Code => (Nat.rfindOpt (search (f M))).Dom :=
    (Partrec.rfindOpt (f := fun M k => search (f M) k)
      (search_primrec.to_comp.comp (hf.comp Computable.fst) Computable.snd)).dom_re
  refine AISafetyAtlas.Computability.nonhalting_not_re i (hre.of_eq fun M => ?_)
  rw [search_dom, hiff]

/-- **The printed construction is false.** `onlyZero` is a non-trivial behavioural
property for which no computable `M ↦ M′` reduces halting to it. -/
theorem literal_false : ¬ LiteralPrint := fun h =>
  literal_false_at 0 (h onlyZero onlyZero_nontrivial 0)

/-! ## Where the witness sits relative to print's judge -/

/-- The computable judge accepting exactly output `0`. -/
def zeroJudge : Judge := fun _ o => decide (o = 0)

theorem zeroJudge_computable : Computable₂ zeroJudge :=
  (PrimrecPred.decide (Primrec.eq.comp Primrec.snd (Primrec.const 0))).to_comp

/-- It is non-trivial in print's sense (`JudgeNontrivial`): `(0, 1)` is rejected and
output `0` is accepted at every input. -/
theorem zeroJudge_nontrivial : JudgeNontrivial zeroJudge :=
  ⟨⟨0, 1, rfl⟩, fun _ => ⟨0, rfl⟩⟩

/-- The witness is `zeroJudge`'s property under the partial-correctness reading:
every output produced is accepted. -/
theorem onlyZero_eq_judge :
    onlyZero = {g | ∀ n, ∀ v ∈ g n, zeroJudge n v = true} := by
  ext g
  simp [onlyZero, zeroJudge]

/-- Under the library's reading of print's judge (`judgeSpec`: every input receives an
accepted output) the nowhere-defined function is never in the property, so the
witness above is not of that form. -/
theorem none_not_mem_judgeSpec (j : Judge) :
    (fun _ => Part.none : ℕ →. ℕ) ∉ judgeSpec j := fun h => by
  obtain ⟨o, ho, -⟩ := h 0
  exact Part.notMem_none o ho

/-- **The repaired construction holds**, as the library proves it
(`halting_reduces_to_spec`): for every non-trivial behavioural property and every
input `i`, a computable `M ↦ M′` with `M′` having `P` exactly when `M` halts on `i`,
or one with `M′` lacking `P` exactly when `M` halts on `i`. -/
theorem repaired_holds (P : SafetySpec) (nontrivial : SpecNontrivial P) (i : ℕ) :
    ∃ f : Agent → Agent, Computable f ∧
      ((∀ M, eval (f M) ∈ P ↔ (eval M i).Dom) ∨
        (∀ M, eval (f M) ∉ P ↔ (eval M i).Dom)) :=
  halting_reduces_to_spec P nontrivial i

end MeloMPrimeLiteral
