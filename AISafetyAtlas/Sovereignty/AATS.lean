module

public import AISafetyAtlas.Sovereignty.Separations

/-!
# Action-based alternating transition systems, and normative ability

`AISafetyAtlas.Sovereignty.Separations` has a **one-step** notion of what a
coalition can force: a `GameForm` is one joint action and one outcome. Wooldridge
and van der Hoek's object runs: states, preconditions on actions, a partial
transition over joint actions, and infinite computations. Every temporal claim in
that paper fails against `GameForm` on that line alone, and section 27 of
`docs/provenance/source-coverage-audit.md` costed all five of its owed rows to
this one object.

M. Wooldridge and W. van der Hoek, *On obligations and normative ability:
Towards a logical analysis of the social contract*, Journal of Applied Logic 3
(2005) 396-420, held as
`wooldridge-van-der-hoek-published-jal-2005-on-obligations-and-normative-ability.pdf`,
sha256 `21970069…`, manifest `SOURCES-2026-09-13-obligations-and-hyperproofs.md`.
Read from rendered images of journal pages 399 to 405, 407 and 410.

## The system, §2

Print's AATS is an `(n + 7)`-tuple `⟨Q, q₀, Ag, Ac₁, …, Ac_n, ρ, τ, Φ, π⟩`.
`AATS` is that tuple, with two differences of encoding and none of content.

* Print says the action sets are **pairwise disjoint** — *"actions are unique to
  agents"* — and then takes their union. `Ac : Ag → Type` makes the
  disjointness structural: the union is the sigma type, and ρ from all actions to sets of states
  is the dependent function `precond`. Nothing has to assume what print has to
  state.
* Print's `τ` is **partial**, and print's coherence constraint (2) says exactly
  which pairs are in its domain. `step` is `Option`-valued and `consistent` is
  that constraint, so the domain is determined rather than carried.

Print's coherence constraint (1), *non-triviality* — *"agents always have at
least one action available"* — is the field `nontrivial`, and it is what makes
`Strategy` inhabited. Print's finiteness of `Q`, `Ag`, each `Ac_i` and `Φ` is
**not** carried: nothing below uses it.

## Computations, §2.1 and §2.2

`options`, `Strategy` with print's legality constraint, `out` for one step and
`comp` for the infinite run, at print's own definitions. `out_univ_subsingleton`
is print's remark that the grand coalition's `out` is a singleton, which here is
a theorem about `step` being a function.

## Normative systems, §3

`Norm` is print's η from all actions to sets of states, **forbidden-primitive and indexed by a
state**. `Sovereignty.NormSystem`, in the `Deontic` module, is a different and
weaker shape — `permitted` and `forbidden` as two predicates on acts alone, with
no state — and `Norm.ofNormSystem` is the embedding that says how: a state-free
norm forbids an act everywhere or nowhere.

`RespectsNature` is print's standing requirement `∀α: (Q \ ρ(α)) ⊆ η(α)`,
*"they forbid anything that is forbidden by 'nature'"*. It is a **predicate
here and a standing assumption in print**, which is the one thing section 27
recorded the atlas as deliberately not having: coupling prohibition to
possibility by fiat would make every norm in the tree inherit a physical
reading. Carrying it as a hypothesis keeps print's results available and leaves
the coupling optional. `Norm.bot` and `Norm.top` are print's `η_⊥` and `η_⊤`,
and `respectsNature_bot` says `η_⊥` is the least norm that respects nature,
which is print's own reading of it.

## Normative ability, §4

`Sat S η C P q` is print's `S, q ⊨ ⟪η : C⟫φ`: some `η`-conformant strategy
profile for `C` whose every computation from `q` satisfies `φ`.

**`φ` is an arbitrary set of computations where print has a path formula.** That
is wider, and it is wider in the direction the results go: print's `|⊨` clauses
for `○`, `◇`, `□` and `𝒰` each carve out a particular set of computations, so
every printed statement about `⟪η : C⟫φ` is an instance. Nothing below inspects
`φ`, which is why the generalisation is free — and it is what lets this module
render §4 without building a temporal logic.

## What is not here

Print's `P_η` and `O_η` (§5), Propositions 3(2) and 3(3), Proposition 4, and the
`⊔`/`⊓` lattice of Proposition 1. Section 27 costs each.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

variable {Q : Type u} {Ag : Type v} {Ac : Ag → Type w} {Φ : Type*}

/-! ## §2: the system -/

/--
**Print's AATS.** States, an initial state, agents with their own actions, an
action precondition function, a partial transition over joint actions, and an
interpretation of atomic propositions.
-/
public structure AATS (Q : Type u) (Ag : Type v) (Ac : Ag → Type w) (Φ : Type*) where
  /-- Print's `q₀`. -/
  init : Q
  /-- Print's `ρ`: the states from which an action may be executed. -/
  precond : ∀ i, Ac i → Set Q
  /-- Print's `τ`, partial: `none` exactly where the joint action is impossible. -/
  step : Q → (∀ i, Ac i) → Option Q
  /-- Print's `π`. -/
  interp : Q → Set Φ
  /-- **Print's coherence constraint (1), non-triviality**: every agent always has
  at least one action available. -/
  nontrivial : ∀ (q : Q) (i : Ag), ∃ α : Ac i, q ∈ precond i α
  /-- **Print's coherence constraint (2), consistency**: `ρ` and `τ` agree on which
  joint actions may be performed. -/
  consistent : ∀ (q : Q) (j : ∀ i, Ac i), (step q j).isSome ↔ ∀ i, q ∈ precond i (j i)

namespace AATS

variable (S : AATS Q Ag Ac Φ)

/-! ## §2.1: strategies -/

/-- **Print's `options(i, q)`**: the actions `i` may perform in `q`. -/
@[expose] public def options (i : Ag) (q : Q) : Set (Ac i) :=
  {α | q ∈ S.precond i α}

/-- Non-triviality, read on `options`. -/
public theorem options_nonempty (i : Ag) (q : Q) : (S.options i q).Nonempty :=
  S.nontrivial q i

/--
**Print's strategy for an agent**, with print's own legality constraint
`σ_i(q) ∈ options(i, q)` carried as a field rather than as a side condition.
-/
public structure Strategy (i : Ag) where
  /-- The action chosen at each state. -/
  act : Q → Ac i
  /-- Print's legality constraint. -/
  legal : ∀ q, act q ∈ S.options i q

/-- **Strategies exist**, by print's non-triviality constraint — which is the
only thing that constraint is for. -/
public theorem nonempty_strategy (i : Ag) : Nonempty (S.Strategy i) :=
  ⟨⟨fun q => (S.nontrivial q i).choose, fun q => (S.nontrivial q i).choose_spec⟩⟩

/-- A strategy profile for a coalition: one strategy per member. -/
public abbrev Profile (C : Set Ag) : Type _ := ∀ i : C, S.Strategy i.1

/--
**Print's `out(σ_C, q)`**: the states that may result from one step at `q` when
the members of `C` act as their strategies say.
-/
@[expose] public def out {C : Set Ag} (σ : S.Profile C) (q : Q) : Set Q :=
  {q' | ∃ j : ∀ i, Ac i, (∀ i : C, j i.1 = (σ i).act q) ∧ S.step q j = some q'}

/--
**The grand coalition's `out` has at most one element**, which is print's remark
that `comp(σ_Ag, q)` is a singleton. Here it is a fact about `step` being a
function: the profile fixes every component of the joint action, so there is
nothing left to vary.
-/
public theorem out_univ_subsingleton (σ : S.Profile Set.univ) (q : Q) :
    (S.out σ q).Subsingleton := by
  rintro a ⟨j, hj, ha⟩ b ⟨k, hk, hb⟩
  have hjk : j = k := funext fun i =>
    (hj ⟨i, trivial⟩).trans (hk ⟨i, trivial⟩).symm
  rw [hjk, hb] at ha
  exact (Option.some_injective _ ha).symm

/-- **And it is non-empty**, because every component is legal and print's
consistency constraint then puts the joint action in the domain of `τ`. -/
public theorem out_univ_nonempty (σ : S.Profile Set.univ) (q : Q) :
    (S.out σ q).Nonempty := by
  have h : (S.step q fun i => (σ ⟨i, trivial⟩).act q).isSome :=
    (S.consistent q _).mpr fun i => (σ ⟨i, trivial⟩).legal q
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp h
  exact ⟨q', ⟨_, fun _ => rfl, hq'⟩⟩

/-! ## §2.2: computations -/

/--
**Print's `comp(σ_C, q)`**: the infinite runs the coalition can be following,
starting at `q`.

`λ[0] = q and ∀u ∈ ℕ: λ[u+1] ∈ out(σ_C, λ[u])`, at print's indices.
-/
@[expose] public def comp {C : Set Ag} (σ : S.Profile C) (q : Q) : Set (ℕ → Q) :=
  {l | l 0 = q ∧ ∀ u, l (u + 1) ∈ S.out σ (l u)}

/-- **The grand coalition's computations are a singleton**, which is print's own
remark. Uniqueness is `out_univ_subsingleton` propagated along the run. -/
public theorem comp_univ_subsingleton (σ : S.Profile Set.univ) (q : Q) :
    (S.comp σ q).Subsingleton := by
  rintro l ⟨hl0, hl⟩ m ⟨hm0, hm⟩
  refine funext fun u => ?_
  induction u with
  | zero => rw [hl0, hm0]
  | succ n ih =>
      exact S.out_univ_subsingleton σ (l n) (hl n) (ih ▸ hm n)

end AATS

/-! ## §3: normative systems -/

/--
**Print's normative system** η from all actions to sets of states: `q ∈ η(α)` means `η` forbids
`α` when the system is in state `q`.

Forbidden-primitive and state-indexed, which is print's shape and not
`Sovereignty.NormSystem`, in the `Deontic` module,'s.
-/
@[expose] public def Norm (Q : Type u) (Ag : Type v) (Ac : Ag → Type w) : Type _ :=
  ∀ i, Ac i → Set Q

namespace Norm

/-- Print's `η_⊥`: forbid exactly what nature forbids. -/
@[expose] public def bot (S : AATS Q Ag Ac Φ) : Norm Q Ag Ac :=
  fun i α => {q | q ∉ S.precond i α}

/-- Print's `η_⊤`: forbid everything everywhere. -/
@[expose] public def top : Norm Q Ag Ac := fun _ _ => Set.univ

/-- Print's `≼`: `η` is at most as restrictive as `η'`. -/
@[expose] public def Le (η η' : Norm Q Ag Ac) : Prop :=
  ∀ i α, η i α ⊆ η' i α

/-- **Print's standing requirement on normative systems**: they forbid anything
that is forbidden by nature. -/
@[expose] public def RespectsNature (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) : Prop :=
  ∀ i α, {q | q ∉ S.precond i α} ⊆ η i α

/-- **Print's *non-trivial***: `η` lets the grand coalition act, everywhere. -/
@[expose] public def IsNontrivial (η : Norm Q Ag Ac) : Prop :=
  ∀ q : Q, ∃ j : ∀ i, Ac i, ∀ i, q ∉ η i (j i)

/-- `≼` is reflexive. -/
public theorem le_refl (η : Norm Q Ag Ac) : Le η η := fun _ _ => subset_rfl

/-- And transitive. -/
public theorem le_trans {η η' η'' : Norm Q Ag Ac} (h : Le η η') (h' : Le η' η'') :
    Le η η'' := fun i α => (h i α).trans (h' i α)

/-- **`η_⊥` respects nature, and is the least norm that does** — which is print's
own reading of it as the most liberal normative system. -/
public theorem respectsNature_bot (S : AATS Q Ag Ac Φ) : RespectsNature S (bot S) :=
  fun _ _ => subset_rfl

/-- **Every norm respecting nature is above `η_⊥`.** -/
public theorem bot_le_of_respectsNature {S : AATS Q Ag Ac Φ} {η : Norm Q Ag Ac}
    (h : RespectsNature S η) : Le (bot S) η := h

/-- **A state-free norm read as print's**: an act is forbidden everywhere or
nowhere. This is the shape `Sovereignty.NormSystem`, in the `Deontic` module,
carries, and the embedding is the precise sense in which it is the special case. -/
@[expose] public def ofActPredicate (forbidden : ∀ i, Ac i → Prop) : Norm Q Ag Ac :=
  fun i α => {_q | forbidden i α}

end Norm

namespace AATS

variable (S : AATS Q Ag Ac Φ)

/-! ## Conformant strategies -/

/-- **Print's `conf(σ_i, η)`**: the strategy never selects a forbidden action. -/
@[expose] public def Conf (η : Norm Q Ag Ac) {i : Ag} (σ : S.Strategy i) : Prop :=
  ∀ q, q ∉ η i (σ.act q)

/-- **Print's `conf(σ_C, η)`**, and so print's `Σ^η_C` as a predicate on profiles. -/
@[expose] public def ConfProfile (η : Norm Q Ag Ac) {C : Set Ag} (σ : S.Profile C) : Prop :=
  ∀ i : C, S.Conf η (σ i)

/--
**Print's Proposition 2, the direction that holds without hypotheses.** A less
restrictive norm admits every profile the more restrictive one does.

Print calls this direction *"obvious"* and proves the converse by contradiction
under non-triviality. This is the half Proposition 3 consumes.
-/
public theorem confProfile_of_le {η η' : Norm Q Ag Ac} (h : Norm.Le η η')
    {C : Set Ag} {σ : S.Profile C} (hσ : S.ConfProfile η' σ) : S.ConfProfile η σ :=
  fun i q hq => hσ i q (h i.1 _ hq)

/--
**Print's Proposition 2, the converse, at one agent.** If every `η'`-conformant
strategy is `η`-conformant then `η ≼ η'`.

Print's own construction: take a state and an action that `η` forbids and `η'`
does not, and edit a conformant strategy to use it there. **The step print does
not name is the legality of the edit** — `σ*_i(q') = α` is a strategy only
because `α` is available at `q'`, and that is exactly print's §3 standing
requirement on `η'` applied at `q' ∉ η'(α)`. So this direction consumes
`RespectsNature`, which print states once and does not cite here.
-/
public theorem le_of_confProfile_singleton {η η' : Norm Q Ag Ac}
    (hnat : Norm.RespectsNature S η') (hnt : Norm.IsNontrivial η')
    (h : ∀ (i : Ag) (σ : S.Strategy i), S.Conf η' σ → S.Conf η σ) :
    Norm.Le η η' := by
  classical
  intro i α q' hq'
  by_contra hq'2
  have hlegal : ∀ (q : Q) (β : Ac i), q ∉ η' i β → β ∈ S.options i q := by
    intro q β hβ
    by_contra hprec
    exact hβ (hnat i β hprec)
  have hlegalα : α ∈ S.options i q' := hlegal q' α hq'2
  have hbase : ∀ q : Q, ∃ β : Ac i, q ∉ η' i β := fun q =>
    ⟨(hnt q).choose i, (hnt q).choose_spec i⟩
  let base : S.Strategy i :=
    { act := fun q => (hbase q).choose
      legal := fun q => hlegal q _ (hbase q).choose_spec }
  let edited : S.Strategy i :=
    { act := fun q => if q = q' then α else base.act q
      legal := fun q => by
        by_cases hq : q = q'
        · subst hq
          simpa using hlegalα
        · simpa [hq] using base.legal q }
  have hconf' : S.Conf η' edited := by
    intro q
    show q ∉ η' i (if q = q' then α else base.act q)
    by_cases hq : q = q'
    · subst hq
      simpa using hq'2
    · simpa [hq] using (hbase q).choose_spec
  have hcontra := h i edited hconf' q'
  have hact : edited.act q' = α := if_pos rfl
  rw [hact] at hcontra
  exact hcontra hq'

/-! ## §4: normative ability -/

/--
**Print's `S, q ⊨ ⟪η : C⟫φ`.** The coalition `C` has an `η`-conformant strategy
profile every one of whose computations from `q` satisfies `φ`.

`φ` is an arbitrary set of computations; print's path formulae each name one.
-/
@[expose] public def Sat (η : Norm Q Ag Ac) (C : Set Ag) (P : Set (ℕ → Q)) (q : Q) : Prop :=
  ∃ σ : S.Profile C, S.ConfProfile η σ ∧ ∀ l ∈ S.comp σ q, l ∈ P

/--
**Normative ability is monotone in the strategy set**, which is the whole
content of print's Proposition 3(1) with the norms abstracted away: `φ` is never
inspected, so anything that supplies more conformant profiles supplies more
ability.
-/
public theorem sat_of_confProfile_mono {η η' : Norm Q Ag Ac} {C : Set Ag}
    (hmono : ∀ σ : S.Profile C, S.ConfProfile η' σ → S.ConfProfile η σ)
    {P : Set (ℕ → Q)} {q : Q} (h : S.Sat η' C P q) : S.Sat η C P q := by
  obtain ⟨σ, hconf, hP⟩ := h
  exact ⟨σ, hmono σ hconf, hP⟩

/--
**Print's Proposition 3(1).** If `η` is less restrictive than `η'`, then
whatever a coalition can bring about within `η'` it can bring about within `η`.

**Wider than print on two axes.** Print states it for *non-trivial* normative
systems, and its proof of this part uses non-triviality nowhere — that
hypothesis belongs to Proposition 2's converse, which this part does not need.
And print concludes about a path formula where this concludes about an arbitrary
set of computations.
-/
public theorem sat_of_le {η η' : Norm Q Ag Ac} (h : Norm.Le η η') {C : Set Ag}
    {P : Set (ℕ → Q)} {q : Q} (hsat : S.Sat η' C P q) : S.Sat η C P q :=
  S.sat_of_confProfile_mono (fun _ => S.confProfile_of_le h) hsat

/-- **Ability within any norm that respects nature implies ability within
`η_⊥`** — Proposition 3(1) at print's most liberal system. -/
public theorem sat_bot_of_respectsNature {η : Norm Q Ag Ac}
    (hnat : Norm.RespectsNature S η) {C : Set Ag} {P : Set (ℕ → Q)} {q : Q}
    (hsat : S.Sat η C P q) : S.Sat (Norm.bot S) C P q :=
  S.sat_of_le (Norm.bot_le_of_respectsNature hnat) hsat

/-! ## §5: permission and obligation

Print derives both from `Sat` at the grand coalition, and that derivation is the
reason this source was fetched: `AISafetyAtlas.Sovereignty.OughtImpliesCan`
carries obligation as a **parameter**, and print carries it as a definition. The
two cannot be compared while only one of them exists here.

`φ` remains an arbitrary set of computations, as in `Sat`, so these inherit that
widening: print's `P_η` and `O_η` are stated over path formulae and every one of
those names such a set.
-/

/--
**Print's `P_η φ ≜ ⟪η : Ag⟫φ`.** `φ` is permissible within `η` when the grand
coalition can cooperate to achieve it while conforming to `η`.
-/
@[expose] public def Perm (η : Norm Q Ag Ac) (P : Set (ℕ → Q)) (q : Q) : Prop :=
  S.Sat η Set.univ P q

/--
**Print's `O_η φ ≜ ¬P_η ¬φ`.** `φ` is obligatory within `η` when its complement
is not permissible — print's *"inevitable if the grand coalition conforms"*.

The negation is set complement, because `φ` here is a set of computations rather
than a formula.
-/
@[expose] public def Oblig (η : Norm Q Ag Ac) (P : Set (ℕ → Q)) (q : Q) : Prop :=
  ¬ S.Perm η Pᶜ q

/-- **Print's Proposition 3(2)**: `S ⊨ P_{η'} φ → P_η φ`. Proposition 3(1) at
the grand coalition, which is all print's proof of it is. -/
public theorem perm_of_le {η η' : Norm Q Ag Ac} (h : Norm.Le η η')
    {P : Set (ℕ → Q)} {q : Q} (hperm : S.Perm η' P q) : S.Perm η P q :=
  S.sat_of_le h hperm

/-- **And so obligation runs the other way.** A *more* restrictive system
obliges more, because it permits less — the contrapositive of Proposition 3(2),
which print does not state and which is the shape a governance argument uses. -/
public theorem oblig_of_le {η η' : Norm Q Ag Ac} (h : Norm.Le η η')
    {P : Set (ℕ → Q)} {q : Q} (hob : S.Oblig η P q) : S.Oblig η' P q :=
  fun hperm => hob (S.perm_of_le h hperm)

/-- Permission is monotone in the objective: achieving a smaller set achieves a
larger one. -/
public theorem perm_mono {η : Norm Q Ag Ac} {P P' : Set (ℕ → Q)} (hsub : P ⊆ P')
    {q : Q} (hperm : S.Perm η P q) : S.Perm η P' q := by
  obtain ⟨σ, hconf, hP⟩ := hperm
  exact ⟨σ, hconf, fun l hl => hsub (hP l hl)⟩

/-- **Half of print's duality**, the half that needs nothing: if either
disjunct is permissible then so is the disjunction. The converse is where the
grand coalition's singleton computation does the work, and it is not proved
here. -/
public theorem perm_union_of_left {η : Norm Q Ag Ac} {P P' : Set (ℕ → Q)} {q : Q}
    (hperm : S.Perm η P q) : S.Perm η (P ∪ P') q :=
  S.perm_mono Set.subset_union_left hperm

/-! ### The top of the lattice, where print's chain breaks

Print's page 410 says the chain `O_η φ → P_η φ` *"does not hold for arbitrary
normative systems"*, and names `η_⊤` as the counterexample: there `O_η φ` holds
for every `φ` while `P_η ψ` holds for no `ψ`. Both halves are below, and the
reason is the same in each: `η_⊤` forbids every action at every state, so no
strategy conforms to it.
-/

/-- Nothing conforms to `η_⊤`: at any state, the action the strategy picks is
forbidden there. The state is a hypothesis rather than an instance, because a
system with no states has nothing to forbid. -/
public theorem not_confProfile_top {C : Set Ag} {i : Ag} (hi : i ∈ C)
    (σ : S.Profile C) (q : Q) : ¬ S.ConfProfile Norm.top σ :=
  fun h => h ⟨i, hi⟩ q (Set.mem_univ _)

/-- **At `η_⊤` nothing is permissible.** -/
public theorem not_perm_top [Nonempty Ag] {P : Set (ℕ → Q)} {q : Q} :
    ¬ S.Perm Norm.top P q := by
  rintro ⟨σ, hconf, -⟩
  exact S.not_confProfile_top (i := Classical.arbitrary Ag) (Set.mem_univ _) σ q hconf

/-- **And at `η_⊤` everything is obligatory**, which is print's own reading of
why the chain fails there: obligation is vacuously total exactly where
permission is empty. -/
public theorem oblig_top [Nonempty Ag] {P : Set (ℕ → Q)} {q : Q} :
    S.Oblig Norm.top P q :=
  S.not_perm_top

end AATS

end AISafetyAtlas.Sovereignty
