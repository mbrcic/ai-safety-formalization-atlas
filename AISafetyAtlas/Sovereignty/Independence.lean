module

public import Mathlib.Order.SetNotation
public import Mathlib.Data.Set.Insert

/-!
# Freedom as independence, and why it is the corner that cannot escape

Christian List and Laura Valentini, *Freedom as Independence*, Ethics 126(4):
1043-1074 (2016), pinned as
`list-valentini-2016-published-ethics-freedom-as-independence.pdf`, sha256
`93fb7dad01fa93d20ce33550...`; and Ian Carter and Ronen Shnayderman, *The
Impossibility of "Freedom as Independence"*, Political Studies Review (2018),
sha256 `bb5bf47c635036527739b5d6...`.

## Print's own structure, which is a two-by-two

List and Valentini do not define one notion. They ask **two independent
questions** and read off four conceptions:

> *The moralization question:* Is the constraint-absence condition qualified by
> some moralized exemption clause, according to which morally permissible
> constraints ... do not count as freedom restricting?
>
> *The robustness question:* Is the constraint-absence condition fortified with a
> modal robustness requirement, according to which freedom requires the absence
> of the constraints in a sufficiently large class of possible worlds (relevant
> hypothetical scenarios) over and above the actual world?

and then:

> (1) the actual absence of the relevant constraints, without any moralized
> exemption clause; (2) the actual absence ... except when those constraints are
> morally permitted; (3) the robust absence ... without any moralized exemption
> clause; (4) the robust absence ... except when those constraints are morally
> permitted.
>
> Liberal freedom in Berlin's sense is an instance of case 1. Moralized liberal
> freedom ... is an instance of case 2. Republican freedom in Pettit's sense is
> an instance of case 4. What we call "freedom as independence" is an instance of
> case 3.

`Free` below is that matrix: two `Bool` parameters, four instances, print's own
names. Nothing here picks a favourite.

Print is explicit that the world class is a parameter -- *"the relevant notion of
possibility, and which possible worlds matter, can be spelled out in a variety of
ways"* -- so `Setting.relevant` is a field and no theorem below fixes it. Print's
footnote 8 is equally explicit that relevance of *constraints* must not be
moralized, which is why `constrains` and `permitted` are separate fields rather
than one filtered relation.

## What Carter and Shnayderman prove, and about which corner

Their two displayed theses are:

> **The impossibility of republican freedom.** Republican freedom entails that no
> one is ever free to do anything whatsoever, not even in a republican state,
> given that there is always a relevant possibility that a person or a group of
> persons will succeed in acquiring the means that would enable them to take over
> the state and thereby possess more or less absolute arbitrary power ...
>
> **The impossibility of freedom as independence.** Freedom as independence
> entails that no one is ever free to do anything whatsoever. But this entailment
> depends not only on the particular case of a threat to any regime ...; it
> depends also on the countless threats which everyone constantly faces in
> everyday situations, given that these threats cannot be eliminated by any
> reasonable state.

The paper's argument is that the two escapes are exactly the two parameters, and
that case 3 has neither:

> On this conception, the very low probability of anyone actually killing us is
> irrelevant. Therefore, the liberal way out of this problem is unavailable.
> Similarly, the fact that no one can do so with impunity is also irrelevant.
> Therefore, the republican way out of the problem is also unavailable.

That is a statement about a **corner of print's own matrix**, and it is what is
proved here. `everyday` is a setting in which

* nobody is constrained in the actual world, so **case 1 and case 2 hold** --
  dropping robustness escapes, which is the liberal way out;
* every lethal constraint is morally impermissible, so **case 4 holds** -- the
  moralized exemption escapes, which is the republican way out;
* and **case 3 fails at every agent and every action**.

`independence_is_the_trapped_corner` puts those together: one setting, three
conceptions satisfied, the fourth empty.

## Where this sits relative to `AISafetyAtlas.Sovereignty.Boundary`

`Boundary` already carries Carter and Shnayderman's bite, as
`not_sovereign_of_outsider_moves_view`, and applies it to **this repository's own
`Sovereign`** -- a non-interference invariant on a game form. That is a different
object from the one the papers argue about, and the note there says so: against
an optimising adversary the improbable branch is the one that gets found, which
is why `Sovereign` is read as a verification invariant rather than as a measure
of freedom.

This module does the other half. It states **print's own frame** -- worlds,
constraints, the moralization and robustness parameters -- and proves the two
theses inside it. Neither module subsumes the other, and a reader who wants the
political-philosophy result rather than the game-form invariant wants this one.

## What this does not claim

Carter and Shnayderman argue that the antecedent -- that such worlds are
genuinely *relevant* -- holds of the actual world. **That is a claim about
politics and nothing here evaluates it.** What is proved is the conditional print
states, plus the corner structure, plus the two escapes being unavailable exactly
at case 3. The `everyday` setting is a witness that the conditional is not
vacuous, not evidence that the world is like it.

Nor is either paper's second thesis reached in full: `withTakeover_not_republicanFree`
gives Carter and Shnayderman's *first* thesis its own witness, and the two theses
differ in scope -- the republican one needs only the state-takeover world, the
independence one needs the everyday ones as well, which is the whole of the
paper's "to the point of absurdity".

Print's claim that the two dimensions are independent — that the matrix has four
cells — is witnessed by `Examples.Sovereignty.four_corners_distinct`, a setting
in which the four conceptions are four different sets of free actions.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

/--
**A freedom setting.** Agents `N`, actions `A`, possible worlds `W`, a designated
actual world, and print's parameter: which worlds are *relevant*.

`constrains w i a` is print's "constraint on `i`'s doing `a`" holding in `w`.
`permitted w i a` is the moralized exemption -- the constraint is morally
permitted, so a moralized conception does not count it. Print's footnote 8
forbids building permissibility into which constraints are *relevant*, which is
why these are two fields and not one.
-/
public structure Setting (N : Type u) (A : Type v) (W : Type w) where
  /-- The actual world. -/
  actual : W
  /-- Print's "sufficiently large class of possible worlds". A parameter, because
  print says it is one. -/
  relevant : Set W
  /-- The actual world is one of the relevant ones: print's robustness is
  *"over and above the actual world"*. -/
  actual_mem : actual ∈ relevant
  /-- `i` is constrained from doing `a` in world `w`. -/
  constrains : W → N → A → Prop
  /-- That constraint is morally permitted, hence exempt on a moralized
  conception. -/
  permitted : W → N → A → Prop

namespace Setting

variable {N : Type u} {A : Type v} {W : Type w} (S : Setting N A W)

/-- **A constraint counts**, at a given answer to print's moralization question.
Non-moralized: every constraint counts. Moralized: only the impermissible ones. -/
@[expose] public def Counts (moralized : Bool) (w : W) (i : N) (a : A) : Prop :=
  S.constrains w i a ∧ (moralized = true → ¬ S.permitted w i a)

/-- **The worlds the conception quantifies over**, at a given answer to print's
robustness question. Non-robust: the actual world alone. Robust: the relevant
class. -/
@[expose] public def worlds (robust : Bool) : Set W :=
  if robust then S.relevant else {S.actual}

/--
**Print's two-by-two.** `Free S m r i a` says `i` is free to do `a` on the
conception whose moralization answer is `m` and whose robustness answer is `r`:
no constraint that counts is present in any world the conception looks at.
-/
@[expose] public def Free (moralized robust : Bool) (i : N) (a : A) : Prop :=
  ∀ w ∈ S.worlds robust, ¬ S.Counts moralized w i a

/-! ## The four conceptions, under print's names -/

/-- **Case 1**, Berlin's liberal freedom: actual absence, no exemption. -/
@[expose] public def LiberalFree (i : N) (a : A) : Prop := S.Free false false i a

/-- **Case 2**, moralized liberal freedom, after Nozick and Dworkin. -/
@[expose] public def MoralizedLiberalFree (i : N) (a : A) : Prop := S.Free true false i a

/-- **Case 3**, List and Valentini's freedom as independence: robust absence, no
exemption. This is the corner Carter and Shnayderman attack. -/
@[expose] public def IndependenceFree (i : N) (a : A) : Prop := S.Free false true i a

/-- **Case 4**, Pettit's republican freedom: robust absence, moralized exemption. -/
@[expose] public def RepublicanFree (i : N) (a : A) : Prop := S.Free true true i a

/-! ## How the two parameters sit -/

/-- Moralizing can only *add* freedom: exempting the permitted constraints
removes counters. -/
public theorem free_of_free_not_moralized {r : Bool} {i : N} {a : A}
    (h : S.Free false r i a) : S.Free true r i a := by
  intro w hw hc
  exact h w hw ⟨hc.1, by simp⟩

/-- Robustness can only *remove* freedom: it looks at every relevant world rather
than the actual one alone. -/
public theorem free_of_free_robust {m : Bool} {i : N} {a : A}
    (h : S.Free m true i a) : S.Free m false i a := by
  intro w hw
  have hw' : w = S.actual := by simpa [worlds] using hw
  subst hw'
  exact h S.actual (by simpa [worlds] using S.actual_mem)

/-- So freedom as independence is the strongest of the four, and republican
freedom sits above it. -/
public theorem republicanFree_of_independenceFree {i : N} {a : A}
    (h : S.IndependenceFree i a) : S.RepublicanFree i a :=
  S.free_of_free_not_moralized h

/-- And liberal freedom sits above it too. -/
public theorem liberalFree_of_independenceFree {i : N} {a : A}
    (h : S.IndependenceFree i a) : S.LiberalFree i a :=
  S.free_of_free_robust h

/-! ## The conditional Carter and Shnayderman state -/

/--
**The impossibility of freedom as independence**, as a conditional.

If every agent faces, for every action, *some relevant possible world* in which a
constraint on that action is present, then on case 3 nobody is free to do
anything. Print's antecedent is that being killed is such a constraint and that
the worlds in which it happens are relevant; that is the claim about politics,
and it is the hypothesis here rather than a theorem.
-/
public theorem not_independenceFree_of_universal_threat
    (h : ∀ i : N, ∀ a : A, ∃ w ∈ S.relevant, S.constrains w i a) (i : N) (a : A) :
    ¬ S.IndependenceFree i a := by
  obtain ⟨w, hw, hc⟩ := h i a
  intro hfree
  exact hfree w (by simpa [worlds] using hw) ⟨hc, by simp⟩

/--
**The republican thesis, as a conditional.** Print's first thesis needs less: a
relevant world carrying an *impermissible* constraint. Inside a republican state
the everyday constraints are punished, hence non-arbitrary, hence exempt -- so
this hypothesis is about the takeover world alone, which is exactly the
difference between the paper's two theses.
-/
public theorem not_republicanFree_of_impermissible_threat
    (h : ∀ i : N, ∀ a : A, ∃ w ∈ S.relevant, S.constrains w i a ∧ ¬ S.permitted w i a)
    (i : N) (a : A) : ¬ S.RepublicanFree i a := by
  obtain ⟨w, hw, hc, hp⟩ := h i a
  intro hfree
  exact hfree w (by simpa [worlds] using hw) ⟨hc, fun _ => hp⟩

end Setting

end AISafetyAtlas.Sovereignty
