module

public import AISafetyAtlas.Sovereignty.Deontic

/-!
# Constitutive rules, and why a Horn derivation is not counts-as

An institution recognizes some acts as creating some facts. The cheapest
formal object for that is a set of **guarded Horn rules** — premises, a trigger
on the act, a conclusion — closed under a least fixed point. This module builds
it, and then proves the thing a reader most needs to know about it.

## The warning this module exists to make mechanical

Jones and Sergot's counts-as connective `⇒ₛ` **deliberately rejects** three
schemas: `RCM` and `RI` at p. 433, and `PTR` at p. 435. The power is not
monotone, is not reflexive, and does not compose.

A least-fixed-point Horn derivation validates two of them:

* `countsAs_refl` — `RI`. Immediate from the `given` constructor.
* `countsAs_trans` — `PTR`. Cut is admissible, by induction on the second
  derivation.

Both are **theorems below**, not remarks. So `Derives` is a perfectly good
derivability relation and a **bad** rendering of counts-as, and a consumer who
reads it as counts-as inherits two schemas the source rejects. That is why the
counts-as reading is given its own name, `CountsAs`, and why the two schemas
are proved about it rather than hidden: the build now says what the docstring
would otherwise only claim.

`RCM` — consequent weakening — is **not expressible** here at all, because
`Fact` is an opaque type with no entailment relation. It is neither validated
nor rejected, and that is recorded rather than glossed.

**What this module does not do:** it does not implement `⇒ₛ`, and it does not
carry the minimal conditional model at p. 435 whose `f_s(α, X) : Set (Set W)` is
the type of `effectivity`. Building that is a separate decision.

## Authority is three things, not one

`Authorized` is a conjunction of three conditions: the institution recognizes
the act, the norms permit it, and it can actually be performed. It is **not**
the conjunction of the three axes `AISafetyAtlas.Sovereignty.Deontic` keeps
apart (empowered, permitted, possible): it uses `Recognized`, not `empowered`.
`authorized_iff` is the decomposition, and `exists_recognized_not_authorized` is
the failure mode — an empowered act the institution recognizes, by firing one of
its own rules, and which is *not* thereby authorized. `Recognized` itself is
weak: `Derives.given` does not look at the act, so a fact that already holds is
recognized for every act. The theorem therefore asks for recognition through a
rule that fires on empowered acts, which is where the act matters.
-/

namespace AISafetyAtlas.Sovereignty

universe u v

/-! ## Guarded Horn constitutive rules -/

/--
**A constitutive rule.** Given the premises, an act meeting `trigger` makes
`conclusion` hold.
-/
public structure ConstitutiveRule (Event : Type u) (Fact : Type v) where
  /-- What must already hold. -/
  premises : List Fact
  /-- Which acts fire the rule. -/
  trigger : Event → Prop
  /-- What the act brings about. -/
  conclusion : Fact

/--
**What an act derives**, as a least fixed point: the ground facts, closed under
firing rules whose premises are themselves derived.

Being a *least* fixed point is what stops an ungrounded cycle from installing
authority on its own — see `no_authority_from_ungrounded_cycles`.
-/
public inductive Derives {E : Type u} {F : Type v}
    (rules : List (ConstitutiveRule E F)) (base : F → Prop) (event : E) : F → Prop
  /-- A ground fact is derived. -/
  | given {f} : base f → Derives rules base event f
  /-- A rule whose trigger fires and whose premises are derived yields its conclusion. -/
  | fire (r) : r ∈ rules → r.trigger event →
      (∀ p, p ∈ r.premises → Derives rules base event p) →
      Derives rules base event r.conclusion

/-- Widening the ground facts can only widen what is derived. -/
public theorem derives_mono_base {E : Type u} {F : Type v}
    {rules : List (ConstitutiveRule E F)} {base base' : F → Prop} {event : E} {f : F}
    (hb : ∀ p, base p → base' p) (h : Derives rules base event f) :
    Derives rules base' event f := by
  induction h with
  | given hp => exact Derives.given (hb _ hp)
  | fire r hr ht _ ih => exact Derives.fire r hr ht ih

/--
**No authority out of nothing.** With no ground facts and no premise-free rule,
nothing is derivable — so a cycle of rules that only ever cite each other
installs no authority.
-/
public theorem no_authority_from_ungrounded_cycles {E : Type u} {F : Type v}
    (rules : List (ConstitutiveRule E F)) (event : E)
    (nonemptyPremises : ∀ r, r ∈ rules → ∃ p, p ∈ r.premises) :
    ∀ f, ¬ Derives rules (fun _ => False) event f := by
  intro f h
  induction h with
  | given hp => exact hp
  | fire r hr _ _ ih =>
      obtain ⟨p, hmem⟩ := nonemptyPremises r hr
      exact ih p hmem

/-! ## The counts-as reading, and the two schemas it validates -/

/--
**The counts-as reading of `Derives`**: `a` counts as `b` for this act when `b`
is derivable from `a` alone.

Named separately, and warned about, because of the next two theorems.
-/
@[expose] public def CountsAs {E : Type u} {F : Type v}
    (rules : List (ConstitutiveRule E F)) (event : E) (a b : F) : Prop :=
  Derives rules (fun f => f = a) event b

/--
**`RI`, which Jones and Sergot reject at p. 433.** Everything counts as itself
here. Their `⇒ₛ` does not validate this.
-/
public theorem countsAs_refl {E : Type u} {F : Type v}
    (rules : List (ConstitutiveRule E F)) (event : E) (a : F) :
    CountsAs rules event a a :=
  Derives.given rfl

/--
**`PTR`, which Jones and Sergot reject at p. 435.** Counts-as composes here.
Their `⇒ₛ` does not validate this either.

The proof is the admissibility of cut for Horn derivability, by induction on the
second derivation.
-/
public theorem countsAs_trans {E : Type u} {F : Type v}
    {rules : List (ConstitutiveRule E F)} {event : E} {a b c : F}
    (hab : CountsAs rules event a b) (hbc : CountsAs rules event b c) :
    CountsAs rules event a c := by
  induction hbc with
  | given hp => exact hp ▸ hab
  | fire r hr ht _ ih => exact Derives.fire r hr ht ih

/--
**The warning, as one statement.** This relation validates both schemas the
source rejects, so it is not that source's connective under any reading.

Stated so that a consumer tempted to cite Jones and Sergot for `CountsAs` meets
a theorem saying why they cannot.
-/
public theorem countsAs_validates_refl_and_trans {E : Type u} {F : Type v}
    (rules : List (ConstitutiveRule E F)) (event : E) :
    (∀ a : F, CountsAs rules event a a) ∧
      (∀ a b c : F, CountsAs rules event a b → CountsAs rules event b c →
        CountsAs rules event a c) :=
  ⟨countsAs_refl rules event, fun _ _ _ => countsAs_trans⟩

/-! ## Authority is three things -/

/--
**An institution**: constitutive rules, the facts that already hold, and the
three-axis setting over the same acts.
-/
public structure Institution (E : Type u) (F : Type v) where
  /-- The constitutive rules. -/
  rules : List (ConstitutiveRule E F)
  /-- The ground facts. -/
  facts : F → Prop
  /-- Permission, institutional power and practical possibility. -/
  setting : InstitutionalSetting E

namespace Institution

variable {E : Type u} {F : Type v} (I : Institution E F)

/-- The institution recognizes that this act brings about this fact. -/
@[expose] public def Recognized (e : E) (f : F) : Prop :=
  Derives I.rules I.facts e f

/--
**Authorized**: recognized, permitted, and practically possible. All three, and
the conjunction is the definition rather than a consequence.
-/
@[expose] public def Authorized (e : E) (f : F) : Prop :=
  I.Recognized e f ∧ I.setting.norms.permitted e ∧ I.setting.possible e

/-- The decomposition, so a consumer can see which component failed. -/
public theorem authorized_iff (e : E) (f : F) :
    I.Authorized e f ↔
      I.Recognized e f ∧ I.setting.norms.permitted e ∧ I.setting.possible e :=
  Iff.rfl

/-- Authorization implies each component separately. -/
public theorem permitted_of_authorized {e : E} {f : F} (h : I.Authorized e f) :
    I.setting.norms.permitted e := h.2.1

/--
**Recognition is not authorization.** Suppose the institution has a rule that
concludes `f` from ground facts and fires on every empowered act. Whenever the
three axes are separated there is an empowered act, possible to perform, that
the institution recognizes as bringing about `f` **by firing that rule**, and
which is nonetheless not authorized — because it is not permitted.

This is `Deontic`'s separation doing work: an act that *counts*, because the
institution's own rule makes it count, is not thereby an act that *may* be done.
(Until 2026-10-05 the hypothesis was that `f` already held, which made every act
"recognized" through `Derives.given` and left only "some act is not permitted";
closure audit.)
-/
public theorem exists_recognized_not_authorized
    (hsep : I.setting.Separated) {r : ConstitutiveRule E F} (hr : r ∈ I.rules)
    (hprem : ∀ p ∈ r.premises, I.facts p) (htrig : ∀ e, I.setting.empowered e → r.trigger e) :
    ∃ e, I.setting.empowered e ∧ I.setting.possible e ∧ I.Recognized e r.conclusion ∧
      ¬ I.Authorized e r.conclusion := by
  obtain ⟨e, hemp, hperm, hposs⟩ := hsep true false true
  have he : I.setting.empowered e := hemp.mpr rfl
  refine ⟨e, he, hposs.mpr rfl,
    Derives.fire r hr (htrig e he) fun p hp => Derives.given (hprem p hp), ?_⟩
  rintro ⟨-, hp, -⟩
  simpa using hperm.mp hp

end Institution

end AISafetyAtlas.Sovereignty
