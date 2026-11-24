import AISafetyAtlas.Computability

/-!
# Alfonseca et al.'s statement of Rice's theorem as printed is false; the repaired one holds

Manuel Alfonseca, Manuel Cebrian, Antonio Fernández Anta, Lorenzo Coviello, Andrés
Abeliuk and Iyad Rahwan, *Superintelligence Cannot be Contained: Lessons from
Computability Theory*, Journal of Artificial Intelligence Research 70 (2021) 65–76,
§5, p. 72 (PDF p. 8; audit row S28-R13):

    This is a consequence of Rice's theorem (Rice, 1953), which states that, any
    non-trivial property (e.g., "harm humans" or "display superintelligence") of a
    Turing machine is undecidable. Non-trivial means some programs have that property
    and some don't.

(Transcribed from the page image in
`docs/provenance/printed-statements/alfonseca-2021-superintelligence-contained.yaml`,
entry `alf21-rice`.) "Undecidable" is the paper's Terminology box (p. 69): no
always-halting algorithm decides it, `¬ ComputablePred` below.

Read literally, the sentence is false. Print restricts the property only by
non-triviality, a condition on programs ("some programs have that property and some
don't"). A syntactic property of programs meets that and can be decidable. This file
proves it for the property "is the program `Code.zero`", whose membership is decided
by comparing codes, which is primitive recursive (`Primrec.eq` on the primitive
recursive encoding of `Nat.Partrec.Code`).

**Modelling choice: the program model.** Print says "Turing machine" and fixes no
formal model. The library, and this file, use Mathlib's `Nat.Partrec.Code`, a
Turing-complete programming language for the partial recursive functions, with
`ComputablePred` as decidability. The witness transfers to any model whose programs
can be compared syntactically by a machine (Turing machines encoded as numbers
included); that transfer is not proved here.

Why the repair is the necessary one and not a different theorem:

* it adds only what print's word "property" means in Rice's theorem: a property of the
  function the program computes, i.e. one that cannot tell apart two programs with the
  same behaviour (`extensional` in `AISafetyAtlas.Computability.rice_code_iff`). Print
  names the theorem it cites, and Rice (1953) is titled "Classes of recursively
  enumerable sets and their decision problems", a statement about what programs
  compute;
* every property print uses it for is of this kind: "harm humans" and "display
  superintelligence" are behaviour, and the examples that follow in §5 (emptiness,
  accepting all strings, the password checker, equivalence) are properties of the
  computed function, as the yaml's note records;
* extensionality excludes the witness, by the library's own theorem: the witness is
  non-trivial and decidable, so `rice_code_iff` forces it to be non-extensional
  (`witness_not_extensional`). That no weaker restriction would do is not claimed.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/rice-literal.lean`. Grading context:
`docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired slips).
-/

open Nat.Partrec (Code)
open AISafetyAtlas.Computability

namespace RiceLiteral

/-- The sentence exactly as printed: every property of programs that some program has
and some program lacks is undecidable. -/
def LiteralPrint : Prop :=
  ∀ C : Set Code, (∃ c, c ∈ C) → (∃ c, c ∉ C) → ¬ ComputablePred fun c => c ∈ C

/-- The witness: the syntactic property "is the program `Code.zero`". -/
def isZero : Set Code := {c | c = Code.zero}

/-- It is decidable: comparing codes is primitive recursive. -/
theorem isZero_computable : ComputablePred fun c => c ∈ isZero :=
  PrimrecPred.computablePred (Primrec.eq.comp Primrec.id (Primrec.const _))

/-- It is non-trivial in print's sense: `Code.zero` has it and `Code.succ` does not. -/
theorem isZero_nontrivial : (∃ c, c ∈ isZero) ∧ ∃ c, c ∉ isZero :=
  ⟨⟨Code.zero, rfl⟩, ⟨Code.succ, fun h => Code.noConfusion h⟩⟩

/-- **The printed sentence is false.** `isZero` is a non-trivial property of programs
whose membership is decidable. -/
theorem not_literalPrint : ¬ LiteralPrint := fun h =>
  h isZero isZero_nontrivial.1 isZero_nontrivial.2 isZero_computable

/-- **The repair is needed, by the library's own theorem.** `isZero` is not extensional:
were it, `rice_code_iff` and its decidability would make it empty or universal. -/
theorem witness_not_extensional :
    ¬ ∀ cf cg, Code.eval cf = Code.eval cg → (cf ∈ isZero ↔ cg ∈ isZero) := fun hext => by
  obtain ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ := isZero_nontrivial
  rcases (rice_code_iff isZero hext).1 isZero_computable with h | h
  · exact (h ▸ h₁ : c₁ ∈ (∅ : Set Code))
  · exact h₂ (h ▸ Set.mem_univ c₂)

/-- **The repaired sentence holds**, as the library proves it: every non-trivial
property of the function a program computes is undecidable. -/
theorem repaired_holds (C : Set Code)
    (extensional : ∀ cf cg, Code.eval cf = Code.eval cg → (cf ∈ C ↔ cg ∈ C))
    (hin : ∃ c, c ∈ C) (hout : ∃ c, c ∉ C) :
    ¬ ComputablePred fun c => c ∈ C := fun hC => by
  obtain ⟨c₁, h₁⟩ := hin
  obtain ⟨c₂, h₂⟩ := hout
  rcases (rice_code_iff C extensional).1 hC with h | h
  · exact (h ▸ h₁ : c₁ ∈ (∅ : Set Code))
  · exact h₂ (h ▸ Set.mem_univ c₂)

end RiceLiteral
