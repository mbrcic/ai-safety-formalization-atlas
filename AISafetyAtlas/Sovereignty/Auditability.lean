module

public import AISafetyAtlas.Sovereignty.Catalogue
public import Mathlib.Logic.Function.Basic

/-!
# What a channel can tell you, and what it cannot

Four results that are all the same picture: a map is determined by a coarser
one exactly when it is constant on that map's fibres. The picture is
elementary; what is worth having is each of the places the proposal puts it,
because each names a different thing that cannot be fixed by trying harder.

## The four

`residualFree_iff_factors` is `C3`, the endorsement condition. A protected
transition that does not depend on the unendorsed channel *is* a transition
that factors through the endorsed interface. Print's hypothesis -- that the
unendorsed input type is nonempty -- is exactly what makes the two directions
meet, and it is a hypothesis here too.

`auditable_iff_exists_detector` is `C9`, exact auditability, and it is
Mathlib's `Function.factorsThrough_iff` under the reading that the label is the
authorship fact and the observation is what a detector gets to see. It is
restated with those names and nothing else; the mathematics is Mathlib's.

`not_exists_recovery_of_collision` is `A3`: two originals that the export
identifies, needing different restorations, defeat every deterministic
recovery. It is the contrapositive of the direction of `C9` that matters
operationally.

`exists_uniformDecision_iff` is `C6`, the observation--action uniformization,
and it is the one that is not immediate. A single decision map obeying the
context-wise requirement exists **iff every observation fibre has an action
good in all of its contexts.** Print calls this the exact one-step boundary
between sufficient evidence and an impossible demand, and the statement earns
that: full state observation is not required, and an observation channel that
merges contexts is harmless exactly when the merged contexts agree on some
action.

`selectionAuditable_iff_separates` is `C10`, monitor selection: a chosen set of
monitors makes the label auditable iff it distinguishes every differently
labelled pair. Print's remark that an empty distinguishing set means even the
complete monitor collection is insufficient is visible in the statement -- the
right-hand side quantifies over pairs, so a pair no monitor separates refutes
every selection at once, the full one included.

## What is not here

`C7`, `C8`, `C11` and the distributional form of `C12` are out of reach: the
first two need a probability layer and the third complexity. See
`docs/provenance/formal-power-proposal-triage.md`, which also records that the
document is unpublished and that nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

/-! ## `C3`: noninterference modulo endorsement -/

/--
**`C3`: the endorsement condition is a factorization.**

`F e j u` is the next protected cognitive state from endorsed evidence `e`, an
authorized instruction `j`, and the unendorsed remainder `u`. Independence of
`u` and factorization through the endorsed interface are the same condition.

The nonemptiness of the unendorsed type is print's hypothesis and it is load
bearing in exactly one direction: without an unendorsed input to evaluate at,
there is nothing to define the factor from.

This permits arbitrarily large authorized changes -- `F'` may depend on `e` as
violently as it likes. What it forbids is any further dependence while `e` and
`j` are held fixed.
-/
public theorem residualFree_iff_factors {E I U S : Type*} [Nonempty U]
    (F : E → I → U → S) :
    (∀ e j u u', F e j u = F e j u') ↔ ∃ F' : E → I → S, ∀ e j u, F e j u = F' e j := by
  classical
  constructor
  · exact fun h => ⟨fun e j => F e j (Classical.arbitrary U),
      fun e j u => h e j u _⟩
  · rintro ⟨F', hF'⟩ e j u u'
    rw [hF', hF']

/-! ## `C9` and `A3`: what a detector can certify -/

/--
**`C9`: exact auditability.** A label is recoverable from an observation
exactly when it is constant on the observation's fibres.

This is `Function.factorsThrough_iff`, stated with the names the proposal uses.
The reading is the content: `ℓ` is the authorship fact -- authorized or not --
and `o` is everything a detector sees. Where authorized and unauthorized cases
are observationally identical, no detector certifies which occurred, and no
amount of care in building the detector changes that.
-/
public theorem auditable_iff_exists_detector {Ξ O L : Type*} [Nonempty L]
    (o : Ξ → O) (ℓ : Ξ → L) :
    (∀ θ θ' : Ξ, o θ = o θ' → ℓ θ = ℓ θ') ↔ ∃ d : O → L, ℓ = d ∘ o :=
  Function.factorsThrough_iff ℓ

/--
**`A3`: lost distinctions obstruct exact recovery.**

Two prior states the export identifies, requiring different restorations,
defeat every deterministic recovery function. Print's proof is function
extensionality and that is what this is; the point is where it applies --
byte-level export is an `o`, and the workflow it must reproduce is an `ℓ`.
-/
public theorem not_exists_recovery_of_collision {Ξ O L : Type*} (o : Ξ → O)
    (ℓ : Ξ → L) {θ θ' : Ξ} (hsame : o θ = o θ') (hdiff : ℓ θ ≠ ℓ θ') :
    ¬ ∃ d : O → L, ℓ = d ∘ o := by
  rintro ⟨d, rfl⟩
  exact hdiff (congrArg d hsame)

/-! ## `C6`: when one decision map suffices -/

/--
**A uniform decision map.** One action per observation, good in every context
that observation is consistent with.
-/
@[expose] public def UniformDecision {Ξ O A : Type*} (o : Ξ → O)
    (Good : Ξ → Set A) (d : O → A) : Prop :=
  ∀ θ : Ξ, d (o θ) ∈ Good θ

/--
**`C6`: the observation--action uniformization.**

A uniform decision map exists iff every observation fibre admits an action that
is good in all of its contexts.

Both directions are one line of mathematics and the statement is the result.
The left side is what a controller must have; the right side is checkable
fibre by fibre without ever constructing the controller, and it does not ask
for the state to be observable. Contexts an observation merges are harmless
exactly when they agree on some action, which is print's "full-state
observation is not necessary".
-/
public theorem exists_uniformDecision_iff {Ξ O A : Type*} [Nonempty A]
    (o : Ξ → O) (Good : Ξ → Set A) :
    (∃ d : O → A, UniformDecision o Good d) ↔
      ∀ θ₀ : Ξ, (⋂ θ ∈ {θ : Ξ | o θ = o θ₀}, Good θ).Nonempty := by
  classical
  constructor
  · rintro ⟨d, hd⟩ θ₀
    refine ⟨d (o θ₀), Set.mem_iInter₂.mpr fun θ hθ => ?_⟩
    have : o θ = o θ₀ := hθ
    exact this ▸ hd θ
  · intro h
    refine ⟨fun ob => if hob : ∃ θ : Ξ, o θ = ob then (h (Classical.choose hob)).some
      else Classical.arbitrary A, fun θ => ?_⟩
    have hob : ∃ θ' : Ξ, o θ' = o θ := ⟨θ, rfl⟩
    dsimp only
    rw [dif_pos hob]
    have hmem := (h (Classical.choose hob)).some_mem
    refine Set.mem_iInter₂.mp hmem θ ?_
    show o θ = o (Classical.choose hob)
    rw [Classical.choose_spec hob]

/-! ## `C10`: which monitors to buy -/

/--
**The observation a selected set of monitors provides.** Each monitor `j` reads
the context; a selection `S` gives the tuple of readings taken over `S`.
-/
@[expose] public def selectionObs {Ξ J O : Type*} (mon : J → Ξ → O) (S : Set J)
    (θ : Ξ) : S → O :=
  fun j => mon j θ

/--
**`C10`: a selection audits the label iff it separates every differently
labelled pair.**

The right-hand side quantifies over pairs of contexts and not over selections,
which is why print's corollary reads off it directly: a pair that **no**
available monitor separates refutes every selection at once, including the
selection that buys every monitor. Cost does not enter, and neither does how
the monitors are combined.
-/
public theorem selectionAuditable_iff_separates {Ξ J O L : Type*}
    (mon : J → Ξ → O) (ℓ : Ξ → L) (S : Set J) :
    (∀ θ θ' : Ξ, selectionObs mon S θ = selectionObs mon S θ' → ℓ θ = ℓ θ') ↔
      ∀ θ θ' : Ξ, ℓ θ ≠ ℓ θ' → ∃ j ∈ S, mon j θ ≠ mon j θ' := by
  constructor
  · intro h θ θ' hne
    by_contra hcon
    refine hne (h θ θ' (funext fun j => ?_))
    by_contra hj
    exact hcon ⟨j, j.2, hj⟩
  · intro h θ θ' hobs
    by_contra hne
    obtain ⟨j, hjS, hj⟩ := h θ θ' hne
    exact hj (congrFun hobs ⟨j, hjS⟩)

/-- Buying more monitors never loses auditability, which is the monotonicity
the separation form makes obvious and the factorization form does not. -/
public theorem selectionAuditable_mono {Ξ J O L : Type*} {mon : J → Ξ → O}
    {ℓ : Ξ → L} {S T : Set J} (hST : S ⊆ T)
    (h : ∀ θ θ' : Ξ, selectionObs mon S θ = selectionObs mon S θ' → ℓ θ = ℓ θ') :
    ∀ θ θ' : Ξ, selectionObs mon T θ = selectionObs mon T θ' → ℓ θ = ℓ θ' := by
  rw [selectionAuditable_iff_separates] at h ⊢
  intro θ θ' hne
  obtain ⟨j, hjS, hj⟩ := h θ θ' hne
  exact ⟨j, hST hjS, hj⟩

/-! ## `C11`: the reduction underneath the hardness claim -/

/--
**The reduction's contexts**: one reference context and one per universe
element. `none` is print's label-`0` reference; `some u` is the label-`1`
context for element `u`.
-/
@[expose] public def coverLabel {U : Type*} : Option U → Prop
  | none => False
  | some _ => True

/--
**The reduction's monitors**: monitor `j` reads `False` at the reference
context and reads membership in `S j` at each element context.
-/
@[expose] public def coverMonitor {U J : Type*} (S : J → Set U) (j : J) :
    Option U → Prop
  | none => False
  | some u => u ∈ S j

/--
**`C11`, the semantics half: a selection audits the reduction instance exactly
when the sets it selects cover the universe.**

This is the correspondence the hardness claim rests on, and it is the half that
is a statement about meaning rather than about machines. The selection is the
*same object* on both sides -- no encoding, no re-indexing -- so any
cardinality or cost function on selections transports unchanged, which is what
"cardinality- and cost-preserving" has to mean before a budget version can be
compared.

What this does **not** establish is `C11` itself. NP-hardness needs the
encoding, the polynomial construction cost, and set cover's own hardness in a
complexity framework the atlas does not carry. This theorem is why only that
half remains.
-/
public theorem cover_iff_selectionAuditable {U J : Type*}
    (S : J → Set U) (T : Set J) :
    (∀ u : U, ∃ j ∈ T, u ∈ S j) ↔
      ∀ θ θ' : Option U,
        selectionObs (coverMonitor S) T θ = selectionObs (coverMonitor S) T θ' →
          coverLabel θ = coverLabel θ' := by
  rw [selectionAuditable_iff_separates]
  constructor
  · rintro h (_ | u) (_ | u') hne
    · exact absurd rfl hne
    · obtain ⟨j, hj, hmem⟩ := h u'
      exact ⟨j, hj, fun hcon => by
        have : (u' ∈ S j) = False := hcon.symm
        exact this ▸ hmem⟩
    · obtain ⟨j, hj, hmem⟩ := h u
      exact ⟨j, hj, fun hcon => by
        have : (u ∈ S j) = False := hcon
        exact this ▸ hmem⟩
    · exact absurd rfl hne
  · intro h u
    obtain ⟨j, hj, hne⟩ := h none (some u) (by
      simp only [coverLabel]
      exact fun hcon => (hcon ▸ trivial : False))
    refine ⟨j, hj, ?_⟩
    by_contra hmem
    exact hne (propext ⟨fun hf => hf.elim, fun hu => absurd hu hmem⟩)

end AISafetyAtlas.Sovereignty
