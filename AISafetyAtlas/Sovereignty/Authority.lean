module

public import AISafetyAtlas.Sovereignty.Disturbance

/-!
# Authority is an input, and these are the links it does not come with

The proposal is explicit that an authority predicate *specifies* an attribution
rule and does not justify it: its §1 correction table says an arbitrary `Auth`
predicate does not establish that it represents anyone's legitimate authority,
and §7.4 says a proof that a machine enforces a constitution is not a proof
that the constitution belongs to the person.

This module takes that literally. **No authority predicate is defined here.**
Every statement quantifies over one, or over a pair of labels, and what is
proved is that certain links between them do not hold. Nothing in the module
can be instantiated to smuggle an attribution rule in, because there is nothing
to instantiate.

## What is proved, and how cheap each one is

`not_exists_label_agreeing_with_both` is `C2`: two constitutions may disagree
about one transition, and then no function of the transition system agrees with
both. Print's proof is one sentence and so is this; the statement is what
matters, because it is the reason an authorship detector needs an authority
specification as an *input* rather than as a conclusion.

`not_authority_implies_control` and `not_control_implies_authority` are `S8`.
These have real content: the witness is the delegated game, where the nominal
owner has no strategy that forces its target and the delegate has one.
`AISafetyAtlas.Examples.Sovereignty.Authority` names the two halves.

`exists_verified_untrue` is `A4` and `exists_all_four_combinations` is `B8`.
Both are one-liners, and that is the honest report: print's own proofs are
one-line countermodels, and what they establish is that linking these
dimensions needs an assumption rather than a relabelling. They are here so that
the claim is in the tree rather than in prose, not because they were hard.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

/-! ## `C2`: authorship is not a function of the dynamics -/

/--
**`C2`: no labelling of transitions agrees with two constitutions that
disagree.**

`label₀` and `label₁` are the authorization labels two constitutions assign to
the same transition system. If they differ anywhere, nothing computed from the
transition alone reproduces both. So a detector that reads only the dynamics
cannot be said to detect authorization; it detects whatever labelling was built
into it.

This is a relativity result and not a claim that legitimacy is unknowable.
-/
public theorem not_exists_label_agreeing_with_both {S A L : Type*}
    (label₀ label₁ : S → A → S → L) {s : S} {a : A} {s' : S}
    (h : label₀ s a s' ≠ label₁ s a s') :
    ¬ ∃ f : S → A → S → L,
      (∀ x y z, f x y z = label₀ x y z) ∧ (∀ x y z, f x y z = label₁ x y z) := by
  rintro ⟨f, h₀, h₁⟩
  exact h ((h₀ s a s').symm.trans (h₁ s a s'))

/-! ## `S8`: authority and effective control are independent -/

/--
**`S8`, first half: formal authority does not imply effective control.**

A nominal owner whose authority predicate holds and who has no strategy forcing
its target. The delegated game is the witness: the principal's guarantee
survives only with the delegate inside the coalition.
-/
public theorem not_authority_implies_control :
    ¬ ∀ (Auth : Bool → Set Bool → Prop) (i : Bool) (A : Set Bool),
      Auth i A → Forces delegateDecides {i} A := by
  intro h
  exact not_retainsAgainst_delegateDecides
    (h (fun i _ => i = false) false {true} rfl)

/--
**`S8`, second half: effective control does not imply formal authority.**

The delegate forces the target and no authority predicate is obliged to say so.
-/
public theorem not_control_implies_authority :
    ¬ ∀ (Auth : Bool → Set Bool → Prop) (i : Bool) (A : Set Bool),
      Forces delegateDecides {i} A → Auth i A := by
  intro h
  have hbad : (true : Bool) = false :=
    h (fun i _ => i = false) true {true} ⟨fun _ => true, fun _ hs => hs ⟨true, rfl⟩⟩
  exact Bool.noConfusion hbad

/-! ## `A4` and `B8`: labels that do not imply one another -/

/--
**`A4`: a signature is not a truth theorem.**

A verifier that accepts a statement which is false. Nothing about the types of
a verification predicate and a truth predicate relates them, so provenance,
factual truth, procedural permission and institutional authority need different
evidence.
-/
public theorem exists_verified_untrue :
    ∃ (Stmt : Type) (verify truth : Stmt → Prop) (s : Stmt), verify s ∧ ¬ truth s :=
  ⟨Unit, fun _ => True, fun _ => False, (), trivial, id⟩

/--
**`B8`: two labels admit all four combinations.**

Whatever the two labels are -- accuracy and authorization, authorship and
privacy, influence and incentive -- nothing in their being labels constrains
which pairs occur. Linking them takes an assumption, not a relabelling.
-/
public theorem exists_all_four_combinations :
    ∃ (E : Type) (p q : E → Prop) (e₀₀ e₀₁ e₁₀ e₁₁ : E),
      (¬ p e₀₀ ∧ ¬ q e₀₀) ∧ (¬ p e₀₁ ∧ q e₀₁) ∧
        (p e₁₀ ∧ ¬ q e₁₀) ∧ (p e₁₁ ∧ q e₁₁) :=
  ⟨Bool × Bool, fun e => e.1 = true, fun e => e.2 = true,
    (false, false), (false, true), (true, false), (true, true),
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

end AISafetyAtlas.Sovereignty
