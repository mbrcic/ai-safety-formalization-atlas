module

public import AISafetyAtlas.Sovereignty.AATS

/-!
# Print's trains, and the normative system that stops them crashing

Wooldridge and van der Hoek's running example, Fig. 2 on journal page 401: two
trains on circular tracks sharing a tunnel, nine reachable states, two actions
each — idling and moving — and a crash state `q₈` from which nothing but idling
is possible.

`trains` is that table. `eta1` is print's Example 2 normative system, whose
stated purpose is *"to ensure that the trains never crash, i.e., that the system
never enters state `q₈`"*, and `sat_noCrash` is that purpose proved: under the
repaired norm, **no** conformant grand-coalition profile can reach `q₈`, at any
state other than `q₈` itself.

## A defect of print, found by rendering Example 2

Print's §3 places a standing requirement on every normative system: `η` must
forbid whatever nature forbids, `∀α: (Q \ ρ(α)) ⊆ η(α)`. Print's own Example 2
does not satisfy it. Print states in words on page 400 that the westbound
move is possible in every state but the crashed one, so nature forbids it at
`q₈` — and print's `η₁` forbids it only at `q₇`. The same holds of the eastbound
move, which `η₁` forbids only at `q₅` and `q₆`.

`not_respectsNature_eta1` is that failure and `not_bot_le_eta1` is its
consequence in print's own lattice: page 404 says *"for any normative system
`η ∈ N`, we have `η_⊥ ≼ η`"*, and `η₁` as printed is below `η_⊥`, so it is not
in `N`.

**It is a slip and not a mistake of substance.** Adding `q₈` to both move actions
repairs it, changes nothing about what the example is for — print says of the
crashed state *"which we need not consider!"* — and `eta1'` is that repair.
`respectsNature_eta1'` and `le_eta1_eta1'` say the repair is a repair and that
it only ever forbids more.

## Proposition 3(1), at print's own pair

`eta2` forbids strictly more than `eta1'`: it also stops the westbound train
entering when both are waiting, which is print's own remark that the asymmetry
of `η₁` could be taken the other way. `sat_noCrash_of_eta2` is Proposition 3(1)
at that pair — ability under the stricter system transfers to the looser one.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-! ## Print's Fig. 2 -/

/-- The nine reachable states of print's train system. -/
public abbrev Station : Type := Fin 9

/-- Two agents: `false` is the eastbound train, `true` the westbound. -/
public abbrev Train : Type := Bool

/-- Two actions each: `false` is idling, `true` is moving. -/
public abbrev Move : Train → Type := fun _ => Bool

/-- Print's joint-action index: `j₀` is both idling, `j₁` is west moving, `j₂` is east moving, `j₃` is both moving. -/
@[expose] public def jointIndex (j : ∀ i, Move i) : Fin 4 :=
  bif j false then (bif j true then 3 else 2) else (bif j true then 1 else 0)

/-- **Print's transition table**, row by row from Fig. 2. The `q₈` row is filled
with `q₈` at the three joint actions print leaves blank; `trainStep` never reads
those entries, because the precondition rules them out. -/
@[expose] public def trainTable (q : Station) (k : Fin 4) : Station :=
  match q, k with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 3 | 0, 3 => 5
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 5 | 1, 3 => 6
  | 2, 0 => 2 | 2, 1 => 0 | 2, 2 => 6 | 2, 3 => 3
  | 3, 0 => 3 | 3, 1 => 5 | 3, 2 => 4 | 3, 3 => 7
  | 4, 0 => 4 | 4, 1 => 7 | 4, 2 => 0 | 4, 3 => 1
  | 5, 0 => 5 | 5, 1 => 6 | 5, 2 => 7 | 5, 3 => 8
  | 6, 0 => 6 | 6, 1 => 3 | 6, 2 => 8 | 6, 3 => 4
  | 7, 0 => 7 | 7, 1 => 8 | 7, 2 => 1 | 7, 3 => 2
  | 8, _ => 8

/-- **Print's `ρ`.** Idling is always possible; moving is possible except once
the trains have crashed. Print leaves `ρ` implicit and says it *"can be read off
from `τ`"*. -/
@[expose] public def precondB (a : Bool) (q : Station) : Bool := !a || q != 8

public abbrev trainPrecond : ∀ i : Train, Move i → Set Station :=
  fun _ a => {q | precondB a q = true}

/-- **Print's `τ`**, partial exactly where a train would move out of the crash
state. -/
@[expose] public def trainStep (q : Station) (j : ∀ i, Move i) : Option Station :=
  if q = 8 ∧ (j false || j true) then none else some (trainTable q (jointIndex j))

/-- **Print's train system as an AATS.** -/
@[expose] public def trains : AATS Station Train Move Unit where
  init := 0
  precond := trainPrecond
  step := trainStep
  interp := fun _ => Set.univ
  nontrivial := fun _ _ => ⟨false, by simp [trainPrecond, precondB]⟩
  consistent := by decide

/-! ## Print's Example 2, and its defect -/

/-- **Print's `η₁`**, transcribed: the eastbound move forbidden at `q₅` and `q₆`, the westbound move
forbidden at `q₇`, idling forbidden nowhere. -/
@[expose] public def eta1B (i : Train) (a : Bool) (q : Station) : Bool :=
  a && (if i then q == 7 else q == 5 || q == 6)

public abbrev eta1 : Norm Station Train Move := fun i a => {q | eta1B i a q = true}

/-- **Print's Example 2 does not satisfy print's §3 standing requirement.**
Nature forbids the eastbound train to move once the trains have crashed, and
`η₁` does not. -/
public theorem not_respectsNature_eta1 : ¬ Norm.RespectsNature trains eta1 := by
  intro h
  have h8 : (8 : Station) ∈ eta1 false true :=
    h false true (show (8 : Station) ∈ {q | q ∉ trainPrecond false true} by decide)
  revert h8
  decide

/-- **And so it is not in print's lattice of normative systems**, which page 404
says has `η_⊥` as its least element. -/
public theorem not_bot_le_eta1 : ¬ Norm.Le (Norm.bot trains) eta1 := by
  intro h
  exact not_respectsNature_eta1 h

/-- **The repair**: add the crash state to both move actions. Print's own reason
for not noticing is on page 403 — the crashed state is the one case it says *"we
need not consider"*. -/
@[expose] public def eta1'B (i : Train) (a : Bool) (q : Station) : Bool :=
  a && (if i then q == 7 || q == 8 else q == 5 || q == 6 || q == 8)

public abbrev eta1' : Norm Station Train Move := fun i a => {q | eta1'B i a q = true}

/-- The repair satisfies print's standing requirement. -/
public theorem respectsNature_eta1' : Norm.RespectsNature trains eta1' := by
  show ∀ (i : Train) (α : Move i) (q : Station), q ∉ trainPrecond i α → q ∈ eta1' i α
  decide

/-- It is above `η_⊥`, as print says every normative system is. -/
public theorem bot_le_eta1' : Norm.Le (Norm.bot trains) eta1' :=
  Norm.bot_le_of_respectsNature respectsNature_eta1'

/-- And it only ever forbids more than print's version. -/
public theorem le_eta1_eta1' : Norm.Le eta1 eta1' := by
  show ∀ (i : Train) (α : Move i) (q : Station), q ∈ eta1 i α → q ∈ eta1' i α
  decide

/-! ## What the norm is for -/

/-- The property print's `η₁` exists to enforce: the trains never crash. -/
@[expose] public def noCrash : Set (ℕ → Station) := {l | ∀ u, l u ≠ 8}

/--
**No conformant joint action leaves a safe state for the crash state.** The
finite check behind everything below: the only transitions into `q₈` are
`τ(q₅, j₃)`, `τ(q₆, j₂)` and `τ(q₇, j₁)`, and the repaired norm forbids the
moving train's action in each.
-/
public theorem step_ne_crash (q : Station) (j : ∀ i, Move i) (hq : q ≠ 8)
    (hconf : ∀ i, q ∉ eta1' i (j i)) : trainStep q j ≠ some 8 := by
  revert hq hconf
  revert q j
  decide

/-- Idling is legal everywhere. -/
@[expose] public def alwaysIdle (i : Train) : trains.Strategy i where
  act := fun _ => false
  legal := fun _ => by simp [trains, AATS.options, trainPrecond, precondB]

/-- Both trains idling: a grand-coalition profile. -/
@[expose] public def bothIdle : trains.Profile Set.univ := fun i => alwaysIdle i.1

/-- It is conformant with the repaired norm, because idling is forbidden
nowhere. -/
public theorem confProfile_bothIdle : trains.ConfProfile eta1' bothIdle := by
  intro i q
  simp [eta1', eta1'B, bothIdle, alwaysIdle]

/--
**Print's Example 2, proved: under the repaired norm the trains do not crash.**

Every computation of a conformant grand-coalition profile from a safe state
stays safe, by induction through `step_ne_crash`.
-/
public theorem noCrash_of_confProfile (σ : trains.Profile Set.univ)
    (hσ : trains.ConfProfile eta1' σ) (q : Station) (hq : q ≠ 8)
    (l : ℕ → Station) (hl : l ∈ trains.comp σ q) : l ∈ noCrash := by
  obtain ⟨hl0, hstep⟩ := hl
  intro u
  induction u with
  | zero => rw [hl0]; exact hq
  | succ n ih =>
      obtain ⟨j, hj, hstepn⟩ := hstep n
      refine fun hcrash => step_ne_crash (l n) j ih (fun i => ?_) ?_
      · rw [hj ⟨i, trivial⟩]
        exact hσ ⟨i, trivial⟩ (l n)
      · exact hstepn.trans (congrArg some hcrash)

/-- **So the grand coalition has the ability, within the repaired norm, to keep
the trains from crashing** — print's `S, q ⊨ ⟪η₁ : Ag⟫□¬crash` at an arbitrary
safe state. -/
public theorem sat_noCrash (q : Station) (hq : q ≠ 8) :
    trains.Sat eta1' Set.univ noCrash q :=
  ⟨bothIdle, confProfile_bothIdle, fun l hl =>
    noCrash_of_confProfile bothIdle confProfile_bothIdle q hq l hl⟩

/-! ## Proposition 3(1) -/

/-- **A stricter norm.** Print remarks that `η₁` is asymmetric — it constrains
the eastbound train where it could equally constrain the westbound — and this
imposes both readings at once. -/
@[expose] public def eta2B (i : Train) (a : Bool) (q : Station) : Bool :=
  a && (if i then q == 5 || q == 7 || q == 8 else q == 5 || q == 6 || q == 8)

public abbrev eta2 : Norm Station Train Move := fun i a => {q | eta2B i a q = true}

public theorem le_eta1'_eta2 : Norm.Le eta1' eta2 := by
  show ∀ (i : Train) (α : Move i) (q : Station), q ∈ eta1' i α → q ∈ eta2 i α
  decide

/-- **Print's Proposition 3(1), at print's own pair**: whatever the coalition can
enforce under the stricter norm it can enforce under the looser one. -/
public theorem sat_noCrash_of_eta2 (q : Station) (C : Set Train)
    (h : trains.Sat eta2 C noCrash q) : trains.Sat eta1' C noCrash q :=
  trains.sat_of_le le_eta1'_eta2 h

/-- And the antecedent is inhabited at the grand coalition, so the transfer is
not vacuous. -/
public theorem sat_noCrash_eta2 (q : Station) (hq : q ≠ 8) :
    trains.Sat eta2 Set.univ noCrash q := by
  refine ⟨bothIdle, ?_, fun l hl =>
    noCrash_of_confProfile bothIdle confProfile_bothIdle q hq l hl⟩
  intro i q'
  simp [eta2, eta2B, bothIdle, alwaysIdle]

/-- The stricter norm also satisfies print's standing requirement. -/
public theorem respectsNature_eta2 : Norm.RespectsNature trains eta2 := by
  show ∀ (i : Train) (α : Move i) (q : Station), q ∉ trainPrecond i α → q ∈ eta2 i α
  decide

/-- And it is non-trivial in print's sense: both trains can always idle. -/
public theorem isNontrivial_eta2 : Norm.IsNontrivial eta2 :=
  fun _ => ⟨fun _ => false, fun i => by simp [eta2, eta2B]⟩

/--
**Print's Proposition 2, the converse, at print's own pair** — and it is a round
trip. Start from `η₁′ ≼ η₂`, read off the inclusion of conformant strategies it
induces, and print's converse returns `η₁′ ≼ η₂`. That is what the proposition
claims: the two characterisations of *less restrictive* agree.

The hypothesis print does not cite is supplied here: `respectsNature_eta2` is
what makes the edited strategy in print's proof legal.
-/
public theorem le_eta1'_eta2_via_strategies : Norm.Le eta1' eta2 :=
  trains.le_of_confProfile_singleton respectsNature_eta2 isNontrivial_eta2
    fun i σ h q hq => h q (le_eta1'_eta2 i (σ.act q) hq)

/-! ## The rest of the library, instantiated -/

/-- Print's non-triviality, read on `options`. -/
public theorem options_nonempty_here (i : Train) (q : Station) :
    (trains.options i q).Nonempty :=
  trains.options_nonempty i q

/-- Strategies exist. -/
public theorem nonempty_strategy_here (i : Train) : Nonempty (trains.Strategy i) :=
  trains.nonempty_strategy i

/-- The grand coalition's one-step outcome is a single state. -/
public theorem out_univ_subsingleton_here (q : Station) :
    (trains.out bothIdle q).Subsingleton :=
  trains.out_univ_subsingleton bothIdle q

/-- And it is non-empty, so `out` at the grand coalition is exactly one state. -/
public theorem out_univ_nonempty_here (q : Station) :
    (trains.out bothIdle q).Nonempty :=
  trains.out_univ_nonempty bothIdle q

/-- Print's remark that `comp(σ_Ag, q)` is a singleton. -/
public theorem comp_univ_subsingleton_here (q : Station) :
    (trains.comp bothIdle q).Subsingleton :=
  trains.comp_univ_subsingleton bothIdle q

/-- `η_⊥` respects nature, and `η_⊤` forbids everything. -/
public theorem respectsNature_bot_here : Norm.RespectsNature trains (Norm.bot trains) :=
  Norm.respectsNature_bot trains

public theorem le_eta2_top : Norm.Le eta2 (Norm.top : Norm Station Train Move) :=
  fun _ _ _ _ => trivial

/-- `≼` is reflexive and transitive, at the norms above. -/
public theorem le_eta1_eta2 : Norm.Le eta1 eta2 :=
  Norm.le_trans le_eta1_eta1' le_eta1'_eta2

public theorem le_refl_eta2 : Norm.Le eta2 eta2 := Norm.le_refl eta2

/-- A state-free norm read as print's, and the state-indexed shape it lands in. -/
@[expose] public def neverMove : Norm Station Train Move :=
  Norm.ofActPredicate fun _ a => a = true

public theorem neverMove_forbids_move (i : Train) (q : Station) :
    q ∈ neverMove i true := rfl

/-- **Ability within a norm that respects nature implies ability within
`η_⊥`.** -/
public theorem sat_bot_noCrash (q : Station) (hq : q ≠ 8) :
    trains.Sat (Norm.bot trains) Set.univ noCrash q :=
  trains.sat_bot_of_respectsNature respectsNature_eta1' (sat_noCrash q hq)

/-- Print's Proposition 2, the direction that holds without hypotheses. -/
public theorem confProfile_eta1'_of_eta2 (σ : trains.Profile Set.univ)
    (h : trains.ConfProfile eta2 σ) : trains.ConfProfile eta1' σ :=
  trains.confProfile_of_le le_eta1'_eta2 h

/-! ## §5: permission and obligation, on the same trains

`Perm` and `Oblig` are print's formula-level operators, and the whole reason
this source was fetched is that `OughtImpliesCan` carries obligation as a
*parameter* where print defines it. A definition that nothing exhibits is not
yet a comparison, so both are run here.

The contrast is the point. At `η₁'` staying off the crashed station is
permissible, so `Perm` is not empty; at `η_⊤` **nothing whatsoever** is
permissible and therefore **everything** is obligatory. That is print's own
page-410 remark that its chain `O_η φ → P_η φ` fails for arbitrary systems, and
it fails by vacuity rather than by a counterexample with content.
-/

/-- **Avoiding the crash is permissible within `η₁'`.** Print's `P_η φ` at a
norm and an objective that are both already here. -/
public theorem perm_noCrash (q : Station) (hq : q ≠ 8) :
    trains.Perm eta1' noCrash q :=
  sat_noCrash q hq

/-- **Print's Proposition 3(2)**, at the two norms this file already orders:
what is permissible under the stricter system is permissible under the laxer
one. -/
public theorem perm_noCrash_of_eta2 (q : Station)
    (h : trains.Perm eta2 noCrash q) : trains.Perm eta1' noCrash q :=
  trains.perm_of_le le_eta1'_eta2 h

/-- And obligation runs the other way along the same pair. -/
public theorem oblig_eta2_of_eta1' (q : Station)
    (h : trains.Oblig eta1' noCrash q) : trains.Oblig eta2 noCrash q :=
  trains.oblig_of_le le_eta1'_eta2 h

/-- Permission is monotone in the objective, at a weakening of `noCrash`. -/
public theorem perm_noCrash_or (q : Station) (hq : q ≠ 8) :
    trains.Perm eta1' (noCrash ∪ {l | l 0 = 8}) q :=
  trains.perm_union_of_left (perm_noCrash q hq)

/-- **At `η_⊤` nothing is permissible** -- not even what `η₁'` permits. -/
public theorem not_perm_top_noCrash (q : Station) :
    ¬ trains.Perm Norm.top noCrash q :=
  trains.not_perm_top

/-- **So at `η_⊤` everything is obligatory.** Print's counterexample to its own
chain, and the contrast with `perm_noCrash` above is what stops it being a
statement about an empty world: some norm on these trains permits something. -/
public theorem oblig_top_noCrash (q : Station) :
    trains.Oblig Norm.top noCrash q :=
  trains.oblig_top

/-- The two really are different norms in this respect, which is the whole of
print's remark. -/
public theorem perm_differs_at_top (q : Station) (hq : q ≠ 8) :
    trains.Perm eta1' noCrash q ∧ ¬ trains.Perm Norm.top noCrash q :=
  ⟨perm_noCrash q hq, not_perm_top_noCrash q⟩

end AISafetyAtlas.Examples.Sovereignty
