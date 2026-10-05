module

public import AISafetyAtlas.Sovereignty.Separations

/-!
# May, may not, can, and is empowered to — four things that are not each other

This module answers a question this repository had left open: **does the atlas
take on "may not" at all?** It does, and the shape of the answer is the content.

## The design decision

`forbidden` is an **independent positive predicate**, not `¬ permitted`. Two
annotations, not one with a negation, which makes four statuses available
rather than two:

| `permitted` | `forbidden` | status |
|---|---|---|
| yes | no | permitted |
| no | yes | forbidden |
| no | no | **unclassified** — the norms are silent |
| yes | yes | **conflicted** — the norms disagree |

The two collapse to the classical reading exactly when the system is both
consistent and complete (`forbidden_iff_not_permitted_iff`), so nothing is lost;
what is gained is that a silent norm system and a self-contradicting one are
different objects, and neither makes everything forbidden. A single
`permitted : E → Prop` with `forbidden := ¬ permitted` cannot express either.

**This is not a deontic logic.** There is no `O`, no `P` operator, no modal
axiom, no possible-worlds semantics, and no inference relation. It is the
minimum vocabulary in which *may not* can be said at all, and it commits the
repository to nothing further.

## The three axes, and the anchor

Jones and Sergot (*A Formal Characterisation of Institutionalised Power*,
J. of the IGPL 4(3):427–443, 1996), abstract, p. 427:

> Following a lead from jurisprudential discussions of *legal power*, we
> distinguish *institutionalised power* from *permission* and *practical
> possibility*.

`InstitutionalSetting` carries those three as separate fields, and
`Separated` is what their sentence means formally: **every combination of the
three is realized somewhere**. That is a theorem with a witness
(`Examples.Sovereignty.Deontic.cube_separated`, all eight combinations over
eight acts), not a naming convention.

The paper's conditional connective `⇒ₛ`, its minimal-model semantics, and its
rejection of `RCM`, `RI` and `PTR` are **not** formalized here; this module
takes only the separation claim. `AISafetyAtlas.Sovereignty.Stability` and the
`effectivity` layer are where the *power* axis already lives — and note that
`Forces` is practical possibility in Jones and Sergot's sense, not
institutionalised power, which is precisely the confusion their abstract exists
to prevent.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

/-! ## Two annotations, four statuses -/

/--
**A norm system**: what is permitted and, independently, what is forbidden.

Both are positive. Neither is defined from the other.
-/
public structure NormSystem (E : Type u) where
  /-- The acts the norms permit. -/
  permitted : E → Prop
  /-- The acts the norms forbid. This is *may not*, and it is not `¬ permitted`. -/
  forbidden : E → Prop

namespace NormSystem

variable {E : Type u} (ν : NormSystem E)

/-- The norms say nothing about this act. -/
@[expose] public def Unclassified (e : E) : Prop := ¬ ν.permitted e ∧ ¬ ν.forbidden e

/-- The norms both permit and forbid this act. -/
@[expose] public def Conflicted (e : E) : Prop := ν.permitted e ∧ ν.forbidden e

/-- Nothing is both permitted and forbidden. -/
@[expose] public def Consistent : Prop := ∀ e, ¬ (ν.permitted e ∧ ν.forbidden e)

/-- Every act is permitted or forbidden. -/
@[expose] public def Complete : Prop := ∀ e, ν.permitted e ∨ ν.forbidden e

/-- Consistency is exactly the absence of conflict. -/
public theorem consistent_iff_no_conflicted : ν.Consistent ↔ ∀ e, ¬ ν.Conflicted e :=
  Iff.rfl

/-- Completeness is exactly the absence of silence. -/
public theorem complete_iff_no_unclassified : ν.Complete ↔ ∀ e, ¬ ν.Unclassified e := by
  constructor
  · rintro h e ⟨hp, hf⟩
    exact (h e).elim hp hf
  · intro h e
    by_contra hc
    push Not at hc
    exact h e ⟨hc.1, hc.2⟩

/--
**The four statuses are exhaustive**: every act is permitted-only,
forbidden-only, unclassified or conflicted.
-/
public theorem status_exhaustive (e : E) :
    (ν.permitted e ∧ ¬ ν.forbidden e) ∨ (¬ ν.permitted e ∧ ν.forbidden e) ∨
      ν.Unclassified e ∨ ν.Conflicted e := by
  by_cases hp : ν.permitted e <;> by_cases hf : ν.forbidden e
  · exact Or.inr (Or.inr (Or.inr ⟨hp, hf⟩))
  · exact Or.inl ⟨hp, hf⟩
  · exact Or.inr (Or.inl ⟨hp, hf⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hp, hf⟩))

/--
**Where the four statuses collapse to two.** A consistent and complete norm
system is exactly one in which *may not* is the negation of *may* — so the
classical reading is a special case, not a rival.
-/
public theorem forbidden_iff_not_permitted_iff :
    (ν.Consistent ∧ ν.Complete) ↔ ∀ e, ν.forbidden e ↔ ¬ ν.permitted e := by
  constructor
  · rintro ⟨hcon, hcom⟩ e
    constructor
    · intro hf hp; exact hcon e ⟨hp, hf⟩
    · intro hnp; exact (hcom e).resolve_left hnp
  · intro h
    refine ⟨fun e hc => ((h e).mp hc.2) hc.1, fun e => ?_⟩
    by_cases hp : ν.permitted e
    · exact Or.inl hp
    · exact Or.inr ((h e).mpr hp)

/-- A silent norm system forbids nothing, and in particular does not forbid
everything. Recorded because "no permission recorded" and "forbidden" are the
two readings this design exists to keep apart. -/
public theorem not_forbidden_of_unclassified {e : E} (h : ν.Unclassified e) :
    ¬ ν.forbidden e := h.2

end NormSystem

/-! ## The three axes Jones and Sergot separate -/

/--
**An institutional setting.** Permission, institutionalised power and practical
possibility, carried as three independent predicates over acts.

`empowered` is Jones and Sergot's *institutionalised power* — the act counts, in
the institution, as creating the state of affairs. `possible` is their
*practical possibility* — it can physically be done. `norms.permitted` is
*permission*. Nothing here relates them, which is the point.
-/
public structure InstitutionalSetting (E : Type u) where
  /-- What is permitted and what is forbidden. -/
  norms : NormSystem E
  /-- The institution recognizes the act as effective. -/
  empowered : E → Prop
  /-- The act can actually be performed. -/
  possible : E → Prop

namespace InstitutionalSetting

variable {E : Type u} (I : InstitutionalSetting E)

/--
**The separation claim, formally.** Every combination of the three axes is
realized: no axis is a consequence of, or incompatible with, any combination of
the others.

This is what Jones and Sergot's abstract asserts when it says the three are
*distinguished*, and it is the strongest form of that claim — weaker forms
("they are not equal") would be satisfied by a setting in which two of them
merely differ on one act.
-/
@[expose] public def Separated : Prop :=
  ∀ b₁ b₂ b₃ : Bool, ∃ e : E,
    (I.empowered e ↔ b₁ = true) ∧ (I.norms.permitted e ↔ b₂ = true) ∧
      (I.possible e ↔ b₃ = true)

/-- **Separation gives the pairwise claims.** Empowerment does not imply
permission, and does not follow from it. -/
public theorem exists_empowered_not_permitted (h : I.Separated) :
    (∃ e, I.empowered e ∧ ¬ I.norms.permitted e) ∧
      (∃ e, I.norms.permitted e ∧ ¬ I.empowered e) := by
  obtain ⟨e₁, h₁, h₂, -⟩ := h true false true
  obtain ⟨e₂, k₁, k₂, -⟩ := h false true true
  exact ⟨⟨e₁, h₁.mpr rfl, fun hp => by simpa using h₂.mp hp⟩,
         ⟨e₂, k₂.mpr rfl, fun he => by simpa using k₁.mp he⟩⟩

/-- **And the one that matters for safety**: an act can be institutionally
effective and not permitted at the same time. A system that only checks whether an
action is *possible* or whether it *counts* has not checked whether it is
allowed. -/
public theorem exists_empowered_possible_not_permitted (h : I.Separated) :
    ∃ e, I.empowered e ∧ I.possible e ∧ ¬ I.norms.permitted e := by
  obtain ⟨e, h₁, h₂, h₃⟩ := h true false true
  exact ⟨e, h₁.mpr rfl, h₃.mpr rfl, fun hp => by simpa using h₂.mp hp⟩

end InstitutionalSetting

/-! ## Two ways to implement a norm, and only one of them touches possibility -/

/--
**Regimentation**: make the bad acts impossible, and leave the norms alone.

This is Grossi, Gabbay and van der Torre's implementation by regimentation
(*The Norm Implementation Problem in Normative Multi-Agent Systems*, ch. 7 of
Dastani, Hindriks & Meyer (eds.), Springer 2010, folio 212), whose model update
deletes transitions:
*R_a^{m'} := R_a^m − {(w, w') | (m,w) ⊨ pre_a & (m,w') ⊨ viol(i)}*,
after which *"it becomes in m' impossible to execute a transition with label
a in pre_a-states leading to a violation state."*
-/
@[expose] public def InstitutionalSetting.regiment {E : Type u}
    (I : InstitutionalSetting E) (bad : E → Prop) : InstitutionalSetting E where
  norms := I.norms
  empowered := I.empowered
  possible := fun e => I.possible e ∧ ¬ bad e

/--
**Perfect enforcement**: forbid the bad acts, and leave what is possible alone.

Grossi, Gabbay and van der Torre, folio 216: enforcement *"is directly deterred
by modifying the payoffs"*, and their model update is **defined by not moving the
transitions** — the printed conditions open *W = W'*, *W_end = W'_end* and
*{R_a} = {R'_a}*. This repository has no payoffs, so what is kept is the axis
claim: the deterrent is recorded in the norms and possibility is untouched.
-/
@[expose] public def InstitutionalSetting.enforce {E : Type u}
    (I : InstitutionalSetting E) (bad : E → Prop) : InstitutionalSetting E where
  norms := { permitted := I.norms.permitted, forbidden := fun e => I.norms.forbidden e ∨ bad e }
  empowered := I.empowered
  possible := I.possible

namespace InstitutionalSetting

variable {E : Type u} (I : InstitutionalSetting E) (bad : E → Prop)

/-- **Regimentation leaves the norms exactly as they were.** -/
public theorem regiment_norms : (I.regiment bad).norms = I.norms := rfl

/-- **Enforcement leaves practical possibility exactly as it was.** This is the
printed `{R_a} = {R'_a}`, and it is the whole difference between the two. -/
public theorem enforce_possible : (I.enforce bad).possible = I.possible := rfl

/-- Neither touches institutional power. -/
public theorem regiment_empowered : (I.regiment bad).empowered = I.empowered := rfl

/-- Neither touches institutional power. -/
public theorem enforce_empowered : (I.enforce bad).empowered = I.empowered := rfl

/-- Enforcement leaves permission alone too; it adds a prohibition. -/
public theorem enforce_permitted :
    (I.enforce bad).norms.permitted = I.norms.permitted := rfl

/-- And that prohibition is exactly the acts it was aimed at. -/
public theorem enforce_forbidden (e : E) :
    (I.enforce bad).norms.forbidden e ↔ (I.norms.forbidden e ∨ bad e) := Iff.rfl

/-- **What regimentation removes.** A regimented act is not possible. -/
public theorem not_possible_of_regimented {e : E} (h : bad e) :
    ¬ (I.regiment bad).possible e := fun hp => hp.2 h

/--
**Regimenting everything unpermitted destroys the separation.**

`Separated` asks for an act that is possible and not permitted. After regimenting
against exactly the unpermitted acts there is none, because possibility now
entails permission. So the three axes are no longer independent — which is the
formal content of *"making violations impossible"*, and the reason regimentation
is not a way of recording a norm but a way of removing the question.
-/
public theorem regiment_unpermitted_not_separated :
    ¬ (I.regiment (fun e => ¬ I.norms.permitted e)).Separated := by
  intro h
  obtain ⟨e, -, hperm, hposs⟩ := h true false true
  exact (hposs.mpr rfl).2 (fun hp => by simpa using hperm.mp hp)

/--
**Enforcement preserves the separation.** Whatever is forbidden, the act that was
empowered, possible and unpermitted still is — so the gap a safety argument has
to close is still there to be closed.
-/
public theorem enforce_separated (h : I.Separated) : (I.enforce bad).Separated := h

/--
**The pair, as one statement.** Both are implementations of the same prohibition
and they differ on exactly one axis: regimentation removes possibility, and after
regimenting against the unpermitted acts nothing is possible-and-unpermitted;
enforcement leaves possibility untouched and the act is still there.
-/
public theorem regiment_and_enforce_differ (h : I.Separated) :
    ¬ (I.regiment (fun e => ¬ I.norms.permitted e)).Separated ∧
      (I.enforce (fun e => ¬ I.norms.permitted e)).Separated :=
  ⟨I.regiment_unpermitted_not_separated, h⟩

end InstitutionalSetting

/-! ## Ought implies can -/

/--
**Ought implies can**, as a condition on a pair of predicates rather than as an
axiom about a modality: nothing obligatory is impossible.

Stated over an arbitrary `obligatory`, because this module deliberately does not
define obligation from `permitted` and `forbidden` — that identification is a
deontic-logic commitment and is not taken here.
-/
@[expose] public def OughtImpliesCan {E : Type u}
    (obligatory possible : E → Prop) : Prop :=
  ∀ e, obligatory e → possible e

/--
**Ought-implies-can does not give permission.** In any setting where the three
axes are separated there is an obligation satisfying ought-implies-can one of
whose obligatory acts is *not permitted*.

So the principle cannot be used to argue that what must be done is thereby
allowed: it constrains obligation against *possibility* only, and permission is
a third axis. The obligation exhibited is the weakest one that could be accused
of triviality -- "whatever can be done, must be" -- which is exactly the case in
which ought-implies-can holds by construction and still buys no permission.
-/
public theorem oughtImpliesCan_does_not_give_permission {E : Type u}
    (I : InstitutionalSetting E) (hsep : I.Separated) :
    ∃ obligatory : E → Prop,
      OughtImpliesCan obligatory I.possible ∧
        ∃ e, obligatory e ∧ ¬ I.norms.permitted e := by
  refine ⟨I.possible, fun _ h => h, ?_⟩
  obtain ⟨e, -, h₂, h₃⟩ := hsep true false true
  exact ⟨e, h₃.mpr rfl, fun hp => by simpa using h₂.mp hp⟩

end AISafetyAtlas.Sovereignty
