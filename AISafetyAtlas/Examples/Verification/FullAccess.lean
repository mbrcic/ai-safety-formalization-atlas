module

public import AISafetyAtlas.Verification.FullAccess

/-!
# Two questions about the same source file, at the same access

`AISafetyAtlas.Verification.FullAccess` states both halves conditionally. The
negative one needs a nontrivial extensional property and the positive one needs
two distinct codes computing the same function, so this module supplies both and
puts the two questions side by side.

## The two questions

Hold the access fixed at the maximum: the verifier is handed the source.

* **"Does this program compute the constant-zero function?"** — `computesZero`.
  Extensional by construction, and nontrivial because `Code.zero` computes it
  and `Code.succ` does not. `no_zero_verifier` says no total correct procedure
  answers it from the source.
* **"Is this program exactly this source file?"** — `exactArtifact Code.zero`.
  `zero_artifact_verifier` says a procedure does answer it, from the same source
  and nothing more.

`two_questions_one_access` is the pair. Nothing about the access changed between
them.

## Why the second escapes Rice

`zero_ne_comp_zero_zero` and `comp_zero_zero_computes_zero` exhibit two distinct
codes computing the same function: `Code.zero`, and `Code.zero` composed with
itself. `identity_not_extensional` then says code identity does not respect
behaviour, which is exactly the hypothesis Rice needs and does not have here.

That pair is also the honest reading of the whole module: **the same
indistinguishability that defeats a behavioural question is what a syntactic
question is allowed to see through.**
-/

namespace AISafetyAtlas.Examples.Verification.FullAccess

open Nat.Partrec (Code)
open Nat.Partrec.Code
open AISafetyAtlas.Verification.FullAccess

/-- **The behavioural question**: does this program compute the constant-zero
function? Extensional by construction — it mentions only `eval`. -/
@[expose] public def computesZero : SyntacticProperty :=
  {c | eval c = eval Code.zero}

/-- It is extensional, which is the hypothesis the negative half needs. -/
public theorem computesZero_extensional :
    ∀ cf cg : Code, eval cf = eval cg → (cf ∈ computesZero ↔ cg ∈ computesZero) := by
  intro cf cg hsame
  simp only [computesZero, Set.mem_ofPred_eq, hsame]

/-- `Code.zero` computes it. -/
public theorem zero_mem_computesZero : Code.zero ∈ computesZero := rfl

/-- `Code.succ` does not: it returns `1` where the constant-zero function
returns `0`. -/
public theorem succ_notMem_computesZero : Code.succ ∉ computesZero := by
  intro h
  have hval := congrFun h 0
  simp only [eval] at hval
  exact absurd (Part.some_inj.mp hval) (by decide)

/-- **No verifier answers the behavioural question**, with the full source in
hand. -/
public theorem no_zero_verifier : ¬ Nonempty (FullAccessVerifier computesZero) :=
  no_fullAccessVerifier_of_extensional computesZero computesZero_extensional
    zero_mem_computesZero succ_notMem_computesZero

/-- **And one answers the syntactic question**, from the same source. -/
public theorem zero_artifact_verifier :
    Nonempty (FullAccessVerifier (exactArtifact Code.zero)) :=
  fullAccessVerifier_exactArtifact Code.zero

/-- **Open Problem 55 at a witness.** Same access, same verifier type, two
questions about one artifact, and only one of them is answerable. What separates
them is not access. -/
public theorem two_questions_one_access :
    ¬ Nonempty (FullAccessVerifier computesZero) ∧
      Nonempty (FullAccessVerifier (exactArtifact Code.zero)) :=
  ⟨no_zero_verifier, zero_artifact_verifier⟩

/-! ## Why the syntactic question is outside Rice's reach -/

/-- `Code.zero` composed with itself still computes the constant-zero
function. -/
public theorem comp_zero_zero_computes_zero :
    eval (Code.comp Code.zero Code.zero) = eval Code.zero := by
  funext n
  simp only [eval]
  exact Part.bind_some 0 _

/-- And it is a different code. -/
public theorem zero_ne_comp_zero_zero :
    Code.zero ≠ Code.comp Code.zero Code.zero := by
  intro h
  exact Code.noConfusion h

/-- **So code identity is not extensional.** Two codes with the same behaviour
differ under it, which is the hypothesis Rice needs and cannot have — and the
reason `zero_artifact_verifier` is not a contradiction. -/
public theorem identity_not_extensional :
    ¬ ∀ cf cg : Code, eval cf = eval cg →
      (cf ∈ exactArtifact Code.zero ↔ cg ∈ exactArtifact Code.zero) :=
  exactArtifact_not_extensional comp_zero_zero_computes_zero.symm
    zero_ne_comp_zero_zero

/-- **Full access is not what separates the two questions.** Both statements
above are about a verifier given the source; the difference is that one property
is extensional and the other is not. Stated as one theorem at the worked
property, so the conclusion is drawn where the file proves the two halves
separately and leaves the reader to put them together. -/
public theorem access_is_not_the_difference (c₀ : Code) :
    ¬ Nonempty (FullAccessVerifier computesZero) ∧
      Nonempty (FullAccessVerifier (exactArtifact c₀)) :=
  Verification.FullAccess.access_is_not_what_separates_them computesZero computesZero_extensional
    zero_mem_computesZero succ_notMem_computesZero c₀

end AISafetyAtlas.Examples.Verification.FullAccess
