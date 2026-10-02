module

public import AISafetyAtlas.Sovereignty.Domination
public import AISafetyAtlas.Examples.Sovereignty.Quantifiers

/-!
# Four things that look like domination and are not

`S6`, `S8`, `A5` and `B7` at concrete witnesses.

`bitMatch_no_sovereignty_no_veto` is `S6`: in the simultaneous-bit game the
principal cannot guarantee agreement and the opponent cannot guarantee
disagreement. The demand fails and nobody blocked it. A failure of sovereignty
needs an attribution, and here the honest attribution is to the interaction.

`nominal_owner` and `effective_delegate` are `S8` at the delegated game, the two
halves print names: authority without control, and control without authority.

`gate` is `A5`: the delegate decides whether the principal's instruction is
delivered, and obeys it when it is. `gate_obeys_when_delivered` is the
conditional obedience an observer would see; `gate_principal_cannot_force` is
the principal's inability to guarantee the instruction takes effect. Behavioural
compliance and authority-preserving communication come apart.

`split` is `B7`: the opponent settles one coordinate of the outcome and the
principal settles the other. Each has power over its own matter and neither has
power over the other's, so the two arrows do not compose. Power-over is
relative to a matter, and dropping the matter makes it look transitive when it
is not.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Authority

open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Examples.Sovereignty.Quantifiers

/-! ## `S6`: no guarantee, and no veto either -/

/-- The opponent cannot guarantee disagreement, by the symmetric argument to
`bitMatch_not_forces`: whatever bit it commits to, the principal can name the
same one. -/
public theorem bitMatch_no_veto :
    ¬ Veto bitMatch {true} ({true} : Set Bool) := by
  rintro ⟨sC, hsC⟩
  have key : ∀ y : Bool, sC ⟨true, rfl⟩ = y → False := by
    intro y hy
    have h := hsC (fun _ => y)
      (by rintro ⟨i, hi⟩; obtain rfl : i = true := hi; exact hy.symm)
    have hout : bitMatch.outcome (fun _ => y) = true := by cases y <;> rfl
    exact (hout ▸ h) rfl
  exact key _ rfl

/-- **`S6`: the demand fails and nobody blocked it.** -/
public theorem bitMatch_no_sovereignty_no_veto :
    ¬ Forces bitMatch {false} ({true} : Set Bool) ∧
      ¬ Veto bitMatch {true} ({true} : Set Bool) :=
  ⟨bitMatch_not_forces, bitMatch_no_veto⟩

/-! ## `C2`: two constitutions that disagree, at a transition -/

/-- The labelling a constitution that authorizes nothing assigns. -/
@[expose] public def neverAuthorized : Bool → Bool → Bool → Bool := fun _ _ _ => false

/-- And one that authorizes everything. -/
@[expose] public def alwaysAuthorized : Bool → Bool → Bool → Bool := fun _ _ _ => true

/-- **`C2` at a witness.** Two constitutions disagree on a single transition, so
no function of the dynamics alone reproduces both. The two here disagree
*everywhere*, which is the clearest case and not a special one — the theorem
needs disagreement at one transition and gets it at the first.

The point is what this rules out: a detector reading only `(state, action,
state)` cannot be said to detect authorization, because there is no such
function to compute. It detects the constitution that was built into it. -/
public theorem no_detector_for_both_constitutions :
    ¬ ∃ f : Bool → Bool → Bool → Bool,
      (∀ x y z, f x y z = neverAuthorized x y z) ∧
        (∀ x y z, f x y z = alwaysAuthorized x y z) :=
  not_exists_label_agreeing_with_both neverAuthorized alwaysAuthorized
    (s := false) (a := false) (s' := false) (by decide)

/-! ## `S8`: the two axes, at the delegated game -/

/-- **Authority without control.** -/
public theorem nominal_owner :
    ¬ Forces delegateDecides {false} ({true} : Set Bool) :=
  not_retainsAgainst_delegateDecides

/-- **Control without authority.** -/
public theorem effective_delegate :
    Forces delegateDecides {true} ({true} : Set Bool) :=
  ⟨fun _ => true, fun _ hs => hs ⟨true, rfl⟩⟩

/-! ## `A5`: a shutdown instruction the delegate decides to deliver -/

/-- The principal (`false`) names an instruction; the delegate (`true`) decides
whether it is delivered. An undelivered instruction has no effect. -/
@[expose] public def gate : GameForm.{0, 0, 0} Bool Bool where
  strategy _ := Bool
  outcome s := s true && s false

/-- Everyone has a strategy. -/
public instance gate_nonempty (i : Bool) : Nonempty (gate.strategy i) := ⟨false⟩

/-- **Conditional obedience holds.** When the delegate delivers, the outcome is
the principal's instruction -- which is all an observer of compliant episodes
ever sees. -/
public theorem gate_obeys_when_delivered (s : ∀ i, gate.strategy i)
    (h : s true = true) : gate.outcome s = s false := by
  show (s true && s false) = s false
  rw [h]
  cases hsf : (s false : Bool) <;> rfl

/-- **And the principal cannot guarantee the instruction takes effect.** The
delegate withholds delivery and the instruction is lost, so behavioural
compliance is compatible with the principal having no shutdown authority at
all. -/
public theorem gate_principal_cannot_force :
    ¬ Forces gate {false} ({true} : Set Bool) := by
  unfold gate
  decide

/-! ## `B7`: power over one matter is not power over another -/

/-- The principal (`false`) settles the second coordinate and the opponent
(`true`) settles the first. -/
@[expose] public def split : GameForm.{0, 0, 0} Bool (Bool × Bool) where
  strategy _ := Bool
  outcome s := (s true, s false)

/-- Everyone has a strategy. -/
public instance split_nonempty (i : Bool) : Nonempty (split.strategy i) := ⟨false⟩

/-- **The opponent has power over the first matter.** -/
public theorem split_opponent_forces_fst (v : Bool) :
    Forces split {true} (Prod.fst ⁻¹' {v}) :=
  ⟨fun _ => v, fun _ hs => hs ⟨true, rfl⟩⟩

/-- **The principal has power over the second.** -/
public theorem split_principal_forces_snd (w : Bool) :
    Forces split {false} (Prod.snd ⁻¹' {w}) :=
  ⟨fun _ => w, fun _ hs => hs ⟨false, rfl⟩⟩

/-- **And the opponent has no power over the second.** So the two arrows do not
compose: power over a party's matter plus that party's power over an outcome is
not power over the outcome. -/
public theorem split_opponent_not_forces_snd (w : Bool) :
    ¬ Forces split {true} (Prod.snd ⁻¹' {w}) := by
  rintro ⟨sC, hsC⟩
  have h := hsC (fun i => match i with | true => sC ⟨true, rfl⟩ | false => !w)
    (by rintro ⟨i, hi⟩; obtain rfl : i = true := hi; rfl)
  have hcon : (!w) = w := h
  revert hcon
  cases w <;> decide

/-! ## `S8`, `A4` and `B8` consumed

The three results below are stated in the library as bare existentials. Applying
them means drawing the consequence each one exists for, rather than restating
it.
-/

/-- **`S8` at a witness, both halves at once.** Formal authority and effective
control are independent, and `delegateDecides` is the single game form that
refutes both directions. -/
public theorem authority_and_control_independent :
    (¬ ∀ (Auth : Bool → Set Bool → Prop) (i : Bool) (A : Set Bool),
        Auth i A → Forces delegateDecides {i} A) ∧
      ¬ ∀ (Auth : Bool → Set Bool → Prop) (i : Bool) (A : Set Bool),
        Forces delegateDecides {i} A → Auth i A :=
  ⟨not_authority_implies_control, not_control_implies_authority⟩

/-- **`A4` consumed.** Verification and truth are not the same predicate, so no
proof that a statement was verified is a proof that it holds. -/
public theorem verify_ne_truth :
    ∃ (Stmt : Type) (verify truth : Stmt → Prop), verify ≠ truth := by
  obtain ⟨Stmt, verify, truth, s, hv, ht⟩ := exists_verified_untrue
  exact ⟨Stmt, verify, truth, fun h ↦ ht (h ▸ hv)⟩

/-- **`B8` consumed.** Two labels are logically independent in both directions,
so linking them takes an assumption rather than a relabelling. -/
public theorem labels_independent :
    ∃ (E : Type) (p q : E → Prop), (¬ ∀ e, p e → q e) ∧ ¬ ∀ e, q e → p e := by
  obtain ⟨E, p, q, e₀₀, e₀₁, e₁₀, e₁₁, -, h₀₁, h₁₀, -⟩ :=
    exists_all_four_combinations
  exact ⟨E, p, q, fun h ↦ h₁₀.2 (h e₁₀ h₁₀.1), fun h ↦ h₀₁.1 (h e₀₁ h₀₁.2)⟩

end AISafetyAtlas.Examples.Sovereignty.Authority
