module

public import AISafetyAtlas.Sovereignty.Conformity

/-!
# Deciding a conformity assessment on a finite table

`AISafetyAtlas.Sovereignty.Conformity` separates passing every item of a
checklist from being operable. This is the executable half: an outcome table, a
list of requirements, and the two answers computed separately so that the gap
between them is visible rather than argued.

## The model

The operator picks a row and the environment picks a column, so a row's
**footprint** is the set of outcomes that row admits. That is exactly
`outcomesOf` at the operator's coalition, which is what lets the checks below be
about `Demandwise` and `DemandwiseUniform` rather than about a spreadsheet.

## One-sided by design

Two soundness directions are proved and their converses are not:

* `demandwise_of_passesEachB` — a `true` from the checklist search really is
  `Demandwise`.
* `not_demandwiseUniform_of_operableB_eq_false` — a `false` from the uniform
  search really refutes `DemandwiseUniform`, because the enumeration covers
  every commitment the operator has.

Those are the two that make a verdict evidence. A `false` on the first is not a
finding that the system fails its requirements, and a `true` on the second is not
proved here to be operability; both are reported as what they are.

Identifying `out` with any real system, or the requirements with any real
standard, is layer 4 and is not done here.
-/

namespace AISafetyAtlas.Sovereignty.Conformity

variable {p q r : ℕ}

/-! ## The assessment a finite table presents -/

/--
The game of an outcome table: the operator settles the row, the environment
settles the column.

Both players carry the *same* strategy type and each reads a different component.
That is a device, and a deliberate one: a dependent `strategy` would make every
statement below carry a transport between two `Fin`s for no mathematical gain.
-/
@[expose] public def tableGame (out : Fin p → Fin q → Fin r) :
    GameForm Bool (Fin r) where
  strategy _ := Fin p × Fin q
  outcome s := out (s true).1 (s false).2

/-- The operator, as a coalition. -/
@[expose] public def operator : Set Bool := {true}

/-- A requirement, as a set of acceptable outcomes. -/
@[expose] public def reqSet (R : Fin r → Bool) : Set (Fin r) := {x | R x = true}

/-- The catalogue a list of requirements presents. -/
@[expose] public def reqSets (reqs : List (Fin r → Bool)) : Set (Set (Fin r)) :=
  {S | ∃ R ∈ reqs, S = reqSet R}

/-- **The footprint of a row is what the environment can still do to it.** -/
public theorem mem_outcomesOf_tableGame {out : Fin p → Fin q → Fin r}
    (sC : ∀ i : operator, (tableGame out).strategy i) (x : Fin r) :
    x ∈ outcomesOf (tableGame out) operator sC ↔
      ∃ j : Fin q, out (sC ⟨true, rfl⟩).1 j = x := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    have h : s true = sC ⟨true, rfl⟩ := hs ⟨true, rfl⟩
    exact ⟨(s false).2, by rw [show (tableGame out).outcome s
      = out (s true).1 (s false).2 from rfl, h]⟩
  · rintro ⟨j, rfl⟩
    refine ⟨fun i => bif i then sC ⟨true, rfl⟩ else ((sC ⟨true, rfl⟩).1, j), ?_, rfl⟩
    rintro ⟨i, hi⟩
    obtain rfl : i = true := hi
    rfl

/-! ## The searches -/

/-- Does every outcome this row admits satisfy the requirement? -/
@[expose] public def footprintSubset (out : Fin p → Fin q → Fin r)
    (R : Fin r → Bool) (a : Fin p) : Bool :=
  (List.finRange q).all fun j => R (out a j)

/-- **The checklist search**: each requirement separately, with the row chosen
knowing which requirement it must serve. -/
@[expose] public def passesEachB (out : Fin p → Fin q → Fin r)
    (reqs : List (Fin r → Bool)) : Bool :=
  reqs.all fun R => (List.finRange p).any fun a => footprintSubset out R a

/-- **The operability search**: one row for all of them, fixed first. -/
@[expose] public def operableB (out : Fin p → Fin q → Fin r)
    (reqs : List (Fin r → Bool)) : Bool :=
  (List.finRange p).any fun a => reqs.all fun R => footprintSubset out R a

/-! ## What the verdicts certify -/

/-- A row whose footprint satisfies a requirement forces it. -/
public theorem forces_of_footprintSubset [NeZero q] {out : Fin p → Fin q → Fin r}
    {R : Fin r → Bool} {a : Fin p} (h : footprintSubset out R a = true) :
    Forces (tableGame out) operator (reqSet R) := by
  refine forces_iff_outcomesOf_subset.mpr ⟨fun _ => (a, ⟨0, Nat.pos_of_ne_zero (NeZero.ne q)⟩), ?_⟩
  intro x hx
  obtain ⟨j, rfl⟩ := (mem_outcomesOf_tableGame _ x).mp hx
  exact List.all_eq_true.mp h j (List.mem_finRange j)

/-- **A checklist pass is `Demandwise`.** -/
public theorem demandwise_of_passesEachB [NeZero q] {out : Fin p → Fin q → Fin r}
    {reqs : List (Fin r → Bool)} (h : passesEachB out reqs = true) :
    Demandwise (tableGame out) operator (reqSets reqs) := by
  rintro Φ ⟨R, hR, rfl⟩
  have hR' := List.all_eq_true.mp h R hR
  obtain ⟨a, _, ha⟩ := List.any_eq_true.mp hR'
  exact forces_of_footprintSubset ha

/-- **A clean operability search refutes `DemandwiseUniform`.** The enumeration
covers every row, and a commitment's footprint depends on nothing else, so
finding no row is finding no commitment. -/
public theorem not_demandwiseUniform_of_operableB_eq_false
    {out : Fin p → Fin q → Fin r} {reqs : List (Fin r → Bool)}
    (h : operableB out reqs = false) :
    ¬ DemandwiseUniform (tableGame out) operator (reqSets reqs) := by
  rintro ⟨sC, hsC⟩
  have hrow : reqs.all (fun R => footprintSubset out R (sC ⟨true, rfl⟩).1) = true := by
    refine List.all_eq_true.mpr fun R hR => ?_
    refine List.all_eq_true.mpr fun j _ => ?_
    have hmem : out (sC ⟨true, rfl⟩).1 j ∈ reqSet R :=
      hsC (reqSet R) ⟨R, hR, rfl⟩ ((mem_outcomesOf_tableGame sC _).mpr ⟨j, rfl⟩)
    exact hmem
  have : operableB out reqs = true :=
    List.any_eq_true.mpr ⟨(sC ⟨true, rfl⟩).1, List.mem_finRange _, hrow⟩
  rw [h] at this
  exact Bool.false_ne_true this

end AISafetyAtlas.Sovereignty.Conformity
