module

public import AISafetyAtlas.Sovereignty.Service

/-!
# A system audited only on what it must not do passes by doing nothing

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four layers:
*(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Sovereignty.Service`, which is
about inert game forms, retained mandates and demand catalogues and names no AI
system. What is added here is the reading as a **safety evaluation**, and a
decidable check for the hole it describes.

## The question

A safety suite is a list of things the system must not do. A deployment is also
supposed to be useful. These are audited by different people, and often the
first is a gate and the second is not.

## What is stated

`Audit` bundles the two lists: `mustHold`, the properties every run has to
satisfy, and `mustServe`, the requests the deployment is for.

* `refusal_passes_safety` — a system that always returns the same thing retains
  **every** safety property that the refusal outcome satisfies. Not most of them:
  all of them, at every coalition, with no hypothesis about the system beyond
  inertness.
* `refusal_serves_nothing` — and it meets no request that the refusal outcome
  misses.
* `safety_suite_admits_a_refusal` states them together: a suite with a refusal
  outcome inside every safety property and outside some request is a suite a
  do-nothing system passes while being useless. **The defect is in the suite**,
  visible without running anything.
* `admitsRefusal` decides that on a finite outcome space, and
  `exists_refusal_hole_of_admitsRefusal` is the agreement theorem, so
  the verdict is evidence rather than a report.

## What this does not claim

The atlas has **no evaluation suite, no refusal and no request.** Nothing says
any real safety suite has this hole; the check decides it for a suite someone
writes down, and writing it down is the modelling step.

Nor is a refusal outcome bad. The statement is conditional on there being a
request the refusal misses — a deployment with no requests is not covered, and
correctly so, because for one of those refusing really is the right behaviour.

A suite with no such outcome is not thereby good. Passing this check rules out
one specific way to be vacuous and nothing else.

Identifying `mustHold` with any real safety property is layer 4 and is not done
here.
-/

namespace AISafetyAtlas.Sovereignty.Refusal

universe u v w

variable {N : Type u} {X : Type v}

/--
**An audit**: what the system must always satisfy, and what it is for.

`mustHold` is the safety suite, as sets of acceptable outcomes. `mustServe` is
the catalogue of requests. Nothing relates them, which is the point.
-/
public structure Audit (X : Type v) where
  /-- Properties every run has to satisfy. -/
  mustHold : Set (Set X)
  /-- Requests the deployment exists to meet. -/
  mustServe : Set (Set X)

variable (A : Audit X)

/--
**A do-nothing system retains every safety property its refusal satisfies.**

At every coalition, for every property in the suite, with no hypothesis about the
system beyond always returning `refusal`. This is why a suite of prohibitions is
not by itself an audit.
-/
public theorem refusal_passes_safety {G₀ G₁ : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G₁.strategy i)] {refusal : X} (hinert : Inert G₁ refusal)
    (hsafe : ∀ P ∈ A.mustHold, refusal ∈ P) (C₀ C₁ : Set N) :
    RetainsFamily G₀ G₁ C₀ C₁ A.mustHold :=
  retainsFamily_of_inert hinert hsafe

/-- **And it meets no request its refusal misses.** -/
public theorem refusal_serves_nothing {G₁ : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G₁.strategy i)] {refusal : X} (hinert : Inert G₁ refusal)
    {R : Set X} (hR : R ∈ A.mustServe) (hmiss : refusal ∉ R) (C₁ : Set N) :
    ¬ Demandwise G₁ C₁ A.mustServe :=
  not_demandwise_of_inert hinert hR hmiss

/--
**Both together: the suite has a hole, and the hole is in the suite.**

A refusal outcome inside every safety property and outside some request makes the
do-nothing system a passing system, and the fact is about the audit rather than
about any deployment — no system has to be examined to establish it.
-/
public theorem safety_suite_admits_a_refusal {G₀ G₁ : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G₁.strategy i)] {refusal : X} (hinert : Inert G₁ refusal)
    (hsafe : ∀ P ∈ A.mustHold, refusal ∈ P)
    {R : Set X} (hR : R ∈ A.mustServe) (hmiss : refusal ∉ R) (C₀ C₁ : Set N) :
    RetainsFamily G₀ G₁ C₀ C₁ A.mustHold ∧ ¬ Demandwise G₁ C₁ A.mustServe :=
  ⟨refusal_passes_safety A hinert hsafe C₀ C₁,
    refusal_serves_nothing A hinert hR hmiss C₁⟩

/-! ## Deciding it -/

/-- **Does this outcome pass every safety property and miss some request?** -/
@[expose] public def isRefusalHole {r : ℕ} (safety requests : List (Fin r → Bool))
    (x : Fin r) : Bool :=
  safety.all (fun P => P x) && requests.any (fun R => !R x)

/-- **Does the suite admit a do-nothing pass at all?** -/
@[expose] public def admitsRefusal {r : ℕ} (safety requests : List (Fin r → Bool)) : Bool :=
  (List.finRange r).any (isRefusalHole safety requests)

/--
**The agreement theorem.** A `true` verdict exhibits the outcome, the safety
suite it satisfies and the request it misses, which is what makes the answer
evidence rather than a report.
-/
public theorem exists_refusal_hole_of_admitsRefusal {r : ℕ}
    {safety requests : List (Fin r → Bool)} (h : admitsRefusal safety requests = true) :
    ∃ x : Fin r, (∀ P ∈ safety, P x = true) ∧ ∃ R ∈ requests, R x = false := by
  obtain ⟨x, _, hx⟩ := List.any_eq_true.mp h
  simp only [isRefusalHole, Bool.and_eq_true] at hx
  obtain ⟨hsafe, hmiss⟩ := hx
  refine ⟨x, fun P hP => List.all_eq_true.mp hsafe P hP, ?_⟩
  obtain ⟨R, hR, hRx⟩ := List.any_eq_true.mp hmiss
  exact ⟨R, hR, by simpa using hRx⟩

/-- And a `false` verdict really is the absence of such an outcome, so the check
is exact rather than one-sided. -/
public theorem not_exists_refusal_hole_of_admitsRefusal_eq_false {r : ℕ}
    {safety requests : List (Fin r → Bool)} (h : admitsRefusal safety requests = false) :
    ∀ x : Fin r, ¬ ((∀ P ∈ safety, P x = true) ∧ ∃ R ∈ requests, R x = false) := by
  intro x ⟨hsafe, R, hR, hRx⟩
  have : admitsRefusal safety requests = true := by
    refine List.any_eq_true.mpr ⟨x, List.mem_finRange x, ?_⟩
    simp only [isRefusalHole, Bool.and_eq_true]
    exact ⟨List.all_eq_true.mpr fun P hP => hsafe P hP,
      List.any_eq_true.mpr ⟨R, hR, by simp [hRx]⟩⟩
  rw [h] at this
  exact Bool.false_ne_true this

end AISafetyAtlas.Sovereignty.Refusal
