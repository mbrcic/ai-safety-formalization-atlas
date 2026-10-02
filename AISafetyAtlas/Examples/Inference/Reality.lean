module

public import AISafetyAtlas.Inference.Reality

/-!
# Wolpert's realities, at the two models the module already builds

`AISafetyAtlas.Inference.Reality` carries Propositions 3 to 5 and Definition 7's
equivalence, and until 2026-09-21 none of them reached an `Examples/`
application — the module had no example file at all. It does build its own two
models, `cycle3Reality` and the infinite copy pair, so most of what is missing is
not a model but the step that runs a general statement at one.

**What is worth saying here is where two results meet.** Each of the
propositions alone is a statement about every reality; put next to the model the
module builds, they pin that model down:

* `cycle3Reality` is pairwise distinguishable and carries a weak-inference
  cycle, by Proposition 3(i). Proposition 3(ii) says no *mutually*
  distinguishable reality carries one. So this reality is **not** mutually
  distinguishable, and the gap between Definition 4's pairwise condition and the
  prose condition before Proposition 3 is a real gap rather than a wording
  choice — `exists_pairwise_not_mutually_distinguishable` is that, and it is the
  fact the two halves of Proposition 3 exist to establish.
* The infinite copy pair copies and strongly infers, by Proposition 5. Its other
  half says copies that strongly infer cannot both have finitely many realized
  setups. So this pair has no such finiteness, and *"only if infinite"* is not a
  hypothesis chosen for convenience.
-/

namespace AISafetyAtlas.Examples.Inference.Reality

open AISafetyAtlas.Inference

/-! ## Proposition 3: the two distinguishability conditions come apart -/

/-- **A pairwise-distinguishable reality with a weak-inference cycle exists**,
which is Proposition 3(i). Named here so the existence claim is consumed rather
than only proved. -/
public theorem exists_weak_cycle :
    ∃ R : DeviceReality.{0, 0} (Fin 4) 3,
      PairwiseDistinguishable R ∧ WeakInferenceCycle R :=
  exists_pairwise_distinguishable_weak_cycle

/--
**And it is not mutually distinguishable.** Proposition 3(ii) forbids a weak
inference cycle in a mutually distinguishable reality, and 3(i) exhibits one in
a pairwise distinguishable reality, so the two conditions are not the same
condition. Wolpert states the second in prose and the first as a proposition;
this is the sentence that makes the pair of them informative.
-/
public theorem exists_pairwise_not_mutually_distinguishable :
    ∃ R : DeviceReality.{0, 0} (Fin 4) 3,
      PairwiseDistinguishable R ∧ ¬ MutuallyDistinguishable R := by
  obtain ⟨R, hpair, hcyc⟩ := exists_pairwise_distinguishable_weak_cycle
  exact ⟨R, hpair, fun hmut => not_mutually_distinguishable_weak_cycle R hmut hcyc⟩

/--
**No reality carries a strong-inference cycle**, at the shape the existence
result above inhabits. Proposition 5's companion: weak inference goes round a
cycle and strong inference does not, so the two notions differ on exactly the
question an oversight chain asks.
-/
public theorem no_strong_cycle_at_three (R : DeviceReality.{0, 0} (Fin 4) 3) :
    ¬ StrongInferenceCycle R :=
  fun hcyc => not_strong_inference_cycle R hcyc

/-! ## Proposition 5: copies, and why the infinite one has to be infinite -/

/-- **Copies that strongly infer exist**, over an infinite universe. -/
public theorem exists_infinite_copies :
    ∃ C₁ C₂ : InferenceDevice.{0, 0} ℕ, Copies C₁ C₂ ∧ StronglyInfers C₁ C₂ :=
  exists_copies_stronglyInfers_infinite

/--
**And they cannot have finitely many realized setups.** The other half of
Proposition 5 says copies that strongly infer are never both finite in that
sense, so the pair above witnesses a class that finiteness would empty. Stated
as the non-existence of the two `Fintype` instances together, which is the form
the impossibility takes.
-/
public theorem infinite_copies_not_both_finite :
    ∀ C₁ C₂ : InferenceDevice.{0, 0} ℕ, Copies C₁ C₂ → StronglyInfers C₁ C₂ →
      ∀ (_ : Fintype {x // C₁.Realized x}) (_ : Fintype {x // C₂.Realized x}), False := by
  intro C₁ C₂ hC hs h₁ h₂
  exact copies_stronglyInfers_not_finite (C₁ := C₁) (C₂ := C₂) hC hs

/-! ## Definition 7: copying is an equivalence -/

/-- **Symmetry**, at the pair the module builds: the second device copies the
first as much as the first copies the second. -/
public theorem infinite_copies_symm : Copies infiniteCopy2 infiniteCopy1 :=
  Copies.symm infiniteCopy_copies

/-- **Transitivity**, through the pair and back. Trivial in content and not in
shape: the composite is what `Copies.trans` builds, and nothing had run it. -/
public theorem infinite_copies_trans : Copies infiniteCopy1 infiniteCopy1 :=
  Copies.trans infiniteCopy_copies infinite_copies_symm

/-- **And mimicry composes**, which is the half of the equivalence that does the
work — `Copies.trans` is two applications of it in opposite directions. -/
public theorem infinite_mimics_trans : Mimics infiniteCopy1 infiniteCopy1 :=
  Mimics.trans infiniteCopy_copies.1 infinite_copies_symm.1

/-- **Proposition 5, the finite half.** Copies *may* one-way weakly infer when
the universe is finite — so the infinite pair above is not the only shape, and
the "only if infinite" of the strong half does not carry over to the weak one.
Distinguishable, copies, and one infers the other. -/
public theorem exists_finite_copies_that_infer :
    ∃ C₁ C₂ : InferenceDevice.{0, 0} (Fin 5),
      Copies C₁ C₂ ∧ Distinguishable C₁ C₂ ∧ InfersDevice C₁ C₂ :=
  exists_copies_distinguishable_weak

end AISafetyAtlas.Examples.Inference.Reality
