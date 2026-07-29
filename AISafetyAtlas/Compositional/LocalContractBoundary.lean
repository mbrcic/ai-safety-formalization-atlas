module

public import AISafetyAtlas.Compositional.Hyperproperties
public import AISafetyAtlas.Compositional.Rectangularity
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.NormNum

/-!
# Boundary: local contracts do not capture relational multiparty goals

Rectangularity and unary coordinate contracts describe **single** joint states
(or single traces): the global predicate factors as a product of per-agent
views.  Many multiparty safety goals are **relational** — they constrain how
two agents' outputs compare, or how several executions of a system relate.

This module records two elementary, machine-checked boundaries used in the
compositional-safety literature (Clarkson–Schneider hyperproperties;
communication-complexity rectangles):

1. **Agreement is not a rectangle.**  Two agents must output the same bit.
   The accepted joint configurations are the diagonal.  That set is not a
   Cartesian product of its projections, and it is not closed under coordinate
   exchange.  Independent local contracts of the form `P₁(a₁) ∧ P₂(a₂)` cannot
   express it.

2. **A 2-safety hyperproperty need not be a pure trace property.**  The
   hyperproperty "the system has at most one complete trace" is `2`-safety under
   the identity observation relation, but it is not of the form
   `{ S | S ⊆ T }` for any fixed set `T` of allowed traces.  Membership depends
   on the whole set of executions, not on each execution in isolation.

These are method limits, not AI-system claims.  They justify why the atlas keeps
both the rectangularity surface and the hyperproperty surface, and why
"verify each agent locally" is incomplete for collusion-style or
multi-execution goals.

No survey coverage row is claimed here; this is compositional infrastructure.
-/

namespace AISafetyAtlas.Compositional.LocalContractBoundary

open AISafetyAtlas.Compositional
open AISafetyAtlas.Compositional.Hyperproperties

/-! ## Boundary 1 — agreement is not a local product contract -/

/--
Two-agent agreement on a Boolean output: the joint configuration lies on the
diagonal.  This is the elementary "both principals must match" constraint.
-/
@[expose] public def Agreement : Set (Bool × Bool) :=
  {p | p.1 = p.2}

/-- Agreement is not closed under mix-and-match coordinate exchange. -/
public theorem not_exchangeClosed_agreement : ¬ ExchangeClosed Agreement := by
  intro h
  have ht : (true, true) ∈ Agreement := by simp [Agreement]
  have hf : (false, false) ∈ Agreement := by simp [Agreement]
  have hmix := h (true, true) ht (false, false) hf
  simp [Agreement] at hmix

/--
**Local-contract boundary (state level).**

Agreement is not a combinatorial rectangle: it is not the product of its
projections.  Therefore it is not expressible as independent unary local
contracts on each agent's output.
-/
public theorem not_isRectangle_agreement : ¬ IsRectangle Agreement := by
  intro h
  exact not_exchangeClosed_agreement
    ((rectangle_iff_exchange_closed Agreement).mp h)

/-- Both projections of agreement are the full Boolean set. -/
public theorem agreement_projections_univ :
    (Prod.fst '' Agreement) = (Set.univ : Set Bool) ∧
      (Prod.snd '' Agreement) = (Set.univ : Set Bool) := by
  constructor
  · apply Set.eq_univ_of_forall
    intro b
    exact ⟨(b, b), by simp [Agreement], rfl⟩
  · apply Set.eq_univ_of_forall
    intro b
    exact ⟨(b, b), by simp [Agreement], rfl⟩

/-- The product of the projections is the full square, strictly larger than the
diagonal. -/
public theorem agreement_ssubset_product_of_projections :
    Agreement ⊂ (Prod.fst '' Agreement) ×ˢ (Prod.snd '' Agreement) := by
  rw [agreement_projections_univ.1, agreement_projections_univ.2]
  constructor
  · intro p hp
    exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  · intro hsub
    have : (true, false) ∈ Agreement := hsub ⟨Set.mem_univ _, Set.mem_univ _⟩
    simp [Agreement] at this

/-! ## Boundary 2 — 2-safety need not be a pure trace property -/

/--
Systems with at most one complete trace.  Membership depends on the *set* of
executions: every singleton is allowed, but a two-point system is not.
-/
@[expose] public def AtMostOneTrace (Trace : Type*) : Hyperproperty Trace :=
  {S | S.Subsingleton}

/--
A hyperproperty is a **pure trace property** when it is exactly the family of
all systems contained in some fixed set `T` of allowed traces.  Equivalently,
membership of a system is decided by checking each of its traces in isolation
against `T`.
-/
@[expose] public def IsPureTraceProperty {Trace : Type*}
    (H : Hyperproperty Trace) : Prop :=
  ∃ T : Set Trace, H = {S | S ⊆ T}

private theorem card_pair_le_two {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).card ≤ 2 := by
  calc
    ({a, b} : Finset α).card ≤ ({b} : Finset α).card + 1 :=
      Finset.card_insert_le a {b}
    _ = 1 + 1 := by simp [Finset.card_singleton]
    _ = 2 := by norm_num

/--
**2-safety of `AtMostOneTrace`.**

Under the identity observation relation (a complete trace is its own prefix),
any system with two distinct traces has a bad observation of size two: those
two traces.  Every system realizing that observation also fails to be a
subsingleton.
-/
public theorem atMostOneTrace_is_two_safety (Trace : Type*) [DecidableEq Trace] :
    IsKSafety (fun p t : Trace => p = t) 2 (AtMostOneTrace Trace) := by
  intro S hS
  have hns : ¬ S.Subsingleton := by
    change S ∉ AtMostOneTrace Trace at hS
    simpa [AtMostOneTrace] using hS
  have hnt : S.Nontrivial := (Set.not_subsingleton_iff (s := S)).1 hns
  rcases hnt with ⟨a, ha, b, hb, hab⟩
  classical
  refine ⟨({a, b} : Observation Trace), card_pair_le_two a b, ?_, ?_⟩
  · intro p hp
    have hp' : p = a ∨ p = b := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hp
    cases hp' with
    | inl h => exact ⟨a, ha, h⟩
    | inr h => exact ⟨b, hb, h⟩
  · intro S' hreal hsub
    change S'.Subsingleton at hsub
    have ha' : a ∈ S' := by
      obtain ⟨t, ht, heq⟩ := hreal a (by simp)
      exact heq ▸ ht
    have hb' : b ∈ S' := by
      obtain ⟨t, ht, heq⟩ := hreal b (by simp)
      exact heq ▸ ht
    exact hab (hsub ha' hb')

/--
**Hyperproperty boundary.**

If the trace type has two distinct values, `AtMostOneTrace` is not a pure trace
property: no single set `T` of allowed traces can decide membership of every
system by per-trace checks alone.  Both singletons are allowed, forcing `T` to
contain two points, but then `T` itself would be an allowed system, contradicting
subsingleton-hood of members of `AtMostOneTrace`.
-/
public theorem not_pureTraceProperty_atMostOneTrace
    {Trace : Type*} (a b : Trace) (hab : a ≠ b) :
    ¬ IsPureTraceProperty (AtMostOneTrace Trace) := by
  rintro ⟨T, hT⟩
  have haS : ({a} : Set Trace) ∈ AtMostOneTrace Trace := by
    simp [AtMostOneTrace]
  have hbS : ({b} : Set Trace) ∈ AtMostOneTrace Trace := by
    simp [AtMostOneTrace]
  have haT : ({a} : Set Trace) ⊆ T := by
    have : ({a} : Set Trace) ∈ {S | S ⊆ T} := by
      rwa [← hT]
    exact this
  have hbT : ({b} : Set Trace) ⊆ T := by
    have : ({b} : Set Trace) ∈ {S | S ⊆ T} := by
      rwa [← hT]
    exact this
  have aT : a ∈ T := haT (Set.mem_singleton a)
  have bT : b ∈ T := hbT (Set.mem_singleton b)
  have hTmem : T ∈ AtMostOneTrace Trace := by
    have : T ∈ {S | S ⊆ T} := Set.Subset.rfl
    rwa [← hT] at this
  have hsub : T.Subsingleton := by
    simpa [AtMostOneTrace] using hTmem
  exact hab (hsub aT bT)

/-- Package: `AtMostOneTrace` on `Bool` is 2-safety and not a pure trace
property. -/
public theorem atMostOneTrace_bool_boundary :
    IsKSafety (fun p t : Bool => p = t) 2 (AtMostOneTrace Bool) ∧
      ¬ IsPureTraceProperty (AtMostOneTrace Bool) :=
  ⟨atMostOneTrace_is_two_safety Bool,
    not_pureTraceProperty_atMostOneTrace false true Bool.false_ne_true⟩

end AISafetyAtlas.Compositional.LocalContractBoundary
