module

public import AISafetyAtlas.Sovereignty.Enforcement

/-!
# Deciding enforceability on a finite regime, and returning the rule

`AISafetyAtlas.Sovereignty.Enforcement` states when a norm cannot be enforced and
proves it by hand. That is the right form for a theorem and the wrong form for
the question a compliance engineer arrives with: *here are the acts, here is what
the log records, here is the rule — can it bind?*

This is the executable half, on the pattern `Knowledge.Check` and
`Oversight.VarietyCheck` already set: a function that computes, and a theorem
saying the function agrees with the `Prop`.

## What runs, and why the negative answer is the cheap one

`findUnenforceable` searches for a forbidden act and a permitted act sharing an
observation. Returning a pair refutes enforceability outright, by
`unenforceable_of_indistinguishable`, and that is the usual shape of a checker in
this repository: a witness, or nothing.

**Returning nothing does more here.** `sanctionOf` is an actual monitoring
rule — flag an observation exactly when some forbidden act produces it — and
`enforces_sanctionOf_of_findUnenforceable_eq_none` proves *that rule* enforces
the norm. So a clean search does not merely fail to find an obstruction: it hands
back the enforcement, already checked. The practitioner gets the monitor, not a
verdict about monitors.

This is the one place in the checker family whose positive answer is
constructive, and it is constructive for a specific reason: the obstruction is a
collision, and the absence of a collision is exactly what makes the obvious rule
correct.

## What does not run

Nothing here decides anything about an infinite act space, and nothing produces a
Lean proof term at runtime. The enum is supplied and its completeness is a
hypothesis, `hcomplete`; a caller that passes a partial enumeration gets an
answer about the acts it listed. Whether a real log schema is `observe`, and
whether a real rule is `forbidden`, are layer-4 assignments and are not made
here or anywhere in the atlas.
-/

namespace AISafetyAtlas.Sovereignty.Enforcement

universe u v

variable {E : Type u} {O : Type v}

/-! ## The regime a pair of decidable predicates presents -/

/--
The regime a Boolean rule and a log map present.

`Regime` carries `Prop`-valued norms because that is what a deontic layer should
carry. A checker reads Booleans. This is the one conversion, kept in one place so
the theorems below are about the same object the search ran on.
-/
@[expose] public def ofBool (forbidden permitted : E → Bool) (observe : E → O) :
    Regime E O where
  norms :=
    { permitted := fun e => permitted e = true
      forbidden := fun e => forbidden e = true }
  observe := observe

/-! ## The search -/

/-- Every ordered pair drawn from an enumeration of the acts. Separate from
`Knowledge.Check.collisionPairs` only in being local; `Finset.toList` is
noncomputable, so the enumeration is an argument here for the same reason. -/
@[expose] public def actPairs (enum : List E) : List (E × E) :=
  enum.flatMap fun e => enum.map fun e' => (e, e')

/--
**Search for an unenforceable pair**: a forbidden act and a permitted act the
log cannot tell apart.
-/
@[expose] public def findUnenforceable [DecidableEq O] (enum : List E)
    (observe : E → O) (forbidden permitted : E → Bool) : Option (E × E) :=
  (actPairs enum).find? fun p =>
    forbidden p.1 && permitted p.2 && observe p.1 == observe p.2

/-- **A returned pair refutes enforceability**, for every response type and every
response function into it. -/
public theorem not_enforces_of_findUnenforceable_eq_some [DecidableEq O]
    {enum : List E} {observe : E → O} {forbidden permitted : E → Bool} {p : E × E}
    (h : findUnenforceable enum observe forbidden permitted = some p) :
    ∀ (S : Type u) (respond : O → S) (benign : S),
      ¬ Enforces (ofBool forbidden permitted observe) respond benign := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨hbad, hgood⟩, hsame⟩ := hp
  exact unenforceable_of_indistinguishable (ofBool forbidden permitted observe)
    hsame hbad hgood

/-! ## The rule a clean search returns -/

/--
**The monitoring rule**: flag an observation exactly when some forbidden act
produces it.

This is the rule anyone would write down. What the theorem below adds is that
when the search is clean it is *correct* — and when the search is not clean, no
rule is, so this is the only one worth writing.
-/
@[expose] public def sanctionOf [DecidableEq O] (enum : List E) (observe : E → O)
    (forbidden : E → Bool) : O → Bool :=
  fun o => enum.any fun e => forbidden e && observe e == o

/--
**A clean search returns an enforcement, not merely the absence of an
obstruction.**

`sanctionOf` sanctions every forbidden act and spares every permitted one, with
`false` as the benign response. The hypothesis `hcomplete` is what makes the
search exhaustive: the rule is built from the enumeration, so an act outside it
is an act the rule never saw.
-/
public theorem enforces_sanctionOf_of_findUnenforceable_eq_none [DecidableEq O]
    {enum : List E} {observe : E → O} {forbidden permitted : E → Bool}
    (hcomplete : ∀ e : E, e ∈ enum)
    (h : findUnenforceable enum observe forbidden permitted = none) :
    Enforces (ofBool forbidden permitted observe)
      (sanctionOf enum observe forbidden) false := by
  have hnone : ∀ q ∈ actPairs enum,
      ¬ (forbidden q.1 && permitted q.2 && observe q.1 == observe q.2) = true := by
    intro q hq
    exact List.find?_eq_none.mp h q hq
  constructor
  · -- every forbidden act is flagged
    intro e hbad
    simp only [ofBool] at hbad ⊢
    have hflag : sanctionOf enum observe forbidden (observe e) = true :=
      List.any_eq_true.mpr ⟨e, hcomplete e, by simp [hbad]⟩
    simp [sanctionOf] at hflag ⊢
    simp [hflag]
  · -- no permitted act is flagged
    intro e hgood
    simp only [ofBool] at hgood ⊢
    by_contra hne
    have hflag : sanctionOf enum observe forbidden (observe e) = true :=
      Bool.not_eq_false _ |>.mp hne
    obtain ⟨e', _, he'⟩ := List.any_eq_true.mp hflag
    simp only [Bool.and_eq_true, beq_iff_eq] at he'
    obtain ⟨hbad', hobs'⟩ := he'
    refine hnone (e', e) ?_ ?_
    · exact List.mem_flatMap.mpr ⟨e', hcomplete e', List.mem_map.mpr ⟨e, hcomplete e, rfl⟩⟩
    · simp [hbad', hgood, hobs']

end AISafetyAtlas.Sovereignty.Enforcement
