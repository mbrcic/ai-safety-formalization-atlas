module

public import AISafetyAtlas.Sovereignty.Communication
public import Mathlib.Logic.Relation

/-!
# Amendment chains, and what a chain is not

A constitution may change, and the proposal's `C5` says what follows when every
change is itself authorized by the constitution in force at the time: every
finite history has a valid authorization chain back to the anchor.

`authorizedFrom_of_stepwise` is that statement, by induction on the length of
the history exactly as print proves it.

`authorizedFrom_of_total` is print's caveat turned into a theorem rather than a
sentence. Print says the result *"proves chain validity only. It does not prove
that the initial anchor is legitimate or that the evidence used for an
amendment was uncompromised."* The formal content of that warning is that
`AuthorizedFrom` constrains nothing at all until the amendment relation does:
under the relation that permits everything, every constitution is authorized
from every other. So a chain is evidence about the amendment rule and about
nothing else.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

variable {K : Type*}

/--
**Authorization from an anchor.** `κ` is reachable from `κ₀` by a finite
sequence of amendments, each permitted by the constitution in force when it was
made.
-/
@[expose] public def AuthorizedFrom (Amend : K → K → Prop) (κ₀ κ : K) : Prop :=
  Relation.ReflTransGen Amend κ₀ κ

/--
**`C5`: a stepwise-authorized history has a valid chain.**

`κ t` is the constitution in force at time `t`, and every step from `t` to
`t + 1` below the horizon has an amendment witness. Then the constitution at
the horizon is authorized from the one at time zero.
-/
public theorem authorizedFrom_of_stepwise {Amend : K → K → Prop} (κ : ℕ → K) :
    ∀ n : ℕ, (∀ t, t < n → Amend (κ t) (κ (t + 1))) → AuthorizedFrom Amend (κ 0) (κ n)
  | 0, _ => Relation.ReflTransGen.refl
  | n + 1, h =>
      (authorizedFrom_of_stepwise κ n fun t ht => h t (Nat.lt_succ_of_lt ht)).tail
        (h n (Nat.lt_succ_self n))

/-- Chains compose, so an authorized continuation of an authorized history is
authorized. -/
public theorem AuthorizedFrom.trans {Amend : K → K → Prop} {κ₀ κ₁ κ₂ : K}
    (h₀ : AuthorizedFrom Amend κ₀ κ₁) (h₁ : AuthorizedFrom Amend κ₁ κ₂) :
    AuthorizedFrom Amend κ₀ κ₂ :=
  Relation.ReflTransGen.trans h₀ h₁

/-- Loosening the amendment rule can only authorize more. -/
public theorem AuthorizedFrom.mono {Amend Amend' : K → K → Prop} {κ₀ κ : K}
    (h : AuthorizedFrom Amend κ₀ κ) (hle : ∀ a b, Amend a b → Amend' a b) :
    AuthorizedFrom Amend' κ₀ κ :=
  Relation.ReflTransGen.mono (fun a b hab => hle a b hab) _ _ h

/--
**What the chain does not give.** Under an amendment rule that permits
everything, every constitution is authorized from every other.

This is print's caveat as a statement: `AuthorizedFrom` is a fact about the
amendment relation, and a valid chain is evidence of legitimacy only to the
extent that the relation already encodes it. Nothing about the anchor, and
nothing about the evidence an amendment was made on, is recoverable from the
chain.
-/
public theorem authorizedFrom_of_total (κ₀ κ : K) :
    AuthorizedFrom (fun _ _ => True) κ₀ κ :=
  Relation.ReflTransGen.single trivial

end AISafetyAtlas.Sovereignty
