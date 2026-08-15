module

public import AISafetyAtlas.Knowledge
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# How much is unknowable — finite fibre ambiguity

`Knowable` is a yes/no question. On finite systems it has a quantitative refinement:
count how many target values remain possible given one observation.

## The trap this module is written around

`Knowable r f ↔ ∀ i, ambiguity r f i ≤ 1` is **not** the content here. It is
`knowable_iff_no_collision` restated in counting form, and a module that stopped
there would be a cardinality wrapper around a theorem the kernel already proves.
It is included as `knowable_iff_ambiguity_le_one` because a bridge to the kernel
belongs in the record, and it is labelled a bridge rather than a result.

The content is the **bounds**:

* `card_image_le_of_knowable` — an observation with fewer outcomes than the
  property has values cannot decode it. A counting obstruction, independent of
  which particular states collide.
* `ambiguity_le_of_comp` — post-processing never lowers ambiguity anywhere. The
  quantitative form of `not_knowable_comp`, which only said the yes/no answer
  could not be repaired.

## Why `≤ 1` and not `= 1`

Ambiguity is `0` at an observation value nothing realizes. Those are exactly the
`i` outside the range of `r`, and requiring `= 1` would make every model with an
unreachable observation value unknowable. The empty fibre carries no ambiguity,
so `≤ 1` is the right exactness condition.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `fibre` | The states an observation value does not separate |
| **Model** | `ambiguity` | How many target values survive one observation |
| **Bridge** | `knowable_iff_ambiguity_le_one` | Exactness ⟺ every fibre carries at most one value |
| **Bound** | `not_knowable_of_one_lt_ambiguity` | One ambiguous fibre refutes knowability |
| **Bound** | `card_image_le_of_knowable` | Knowability needs at least as many observation outcomes as target values |
| **Bound** | `not_knowable_of_card_lt` | Its contrapositive: the counting obstruction |
| **Bound** | `ambiguity_le_of_comp` | Coarsening never decreases ambiguity |

## Constructivity

Every declaration here is classical — `[propext, Classical.choice, Quot.sound]`
— including the two bounds, which are otherwise elementary. That is inherited
from Mathlib's `Finset`/`Fintype` development, not from anything in the
statements. It is a real difference from the kernel, where
`not_knowable_of_collision`, `Knowable.mono` and `not_knowable_comp` depend on no
axioms at all, and it is recorded here so nobody infers constructivity from the
finiteness.

## Explicit non-claims

Finite counting only. There is no probability, no entropy, no rate, and no
measure here: `ambiguity` counts possibilities, it does not weigh them. A
conditional-entropy treatment would need Shannon entropy over general probability
spaces, which Mathlib does not carry at the pinned revision — it has topological
entropy, binary entropy and Kullback–Leibler divergence, and no conditional
Shannon entropy. That is a separate foundation, not an extension of this module.

No survey coverage row is claimed here; this is workbench infrastructure.
-/

namespace AISafetyAtlas.Knowledge

universe u v w

variable {Ω : Type u} {I : Type v} {Y : Type w}

/-! ## Counting what an observation leaves open -/

/-- The states that share one observation value: the fibre `r` cannot see into. -/
@[expose] public def fibre [Fintype Ω] [DecidableEq I]
    (r : Ω → I) (i : I) : Finset Ω :=
  Finset.univ.filter (fun ω => r ω = i)

/--
The **ambiguity** of an observation value: how many distinct target values are
still possible once the observation reads `i`.

`1` is exact knowledge, `0` means nothing realizes `i`, and anything larger is
the shortfall. This is the quantity a yes/no `Knowable` collapses.
-/
@[expose] public def ambiguity [Fintype Ω] [DecidableEq I] [DecidableEq Y]
    (r : Ω → I) (f : Ω → Y) (i : I) : ℕ :=
  ((fibre r i).image f).card

/-! ## Bridge to the kernel -/

/--
Exactness is ambiguity at most one, everywhere.

A **bridge**, not a result: this is `knowable_iff_no_collision` in counting form.
It earns its place by letting the bounds below talk to `Knowable`, not by adding
mathematical content.
-/
public theorem knowable_iff_ambiguity_le_one
    [Fintype Ω] [DecidableEq I] [DecidableEq Y] [Nonempty Y]
    (r : Ω → I) (f : Ω → Y) :
    Knowable r f ↔ ∀ i, ambiguity r f i ≤ 1 := by
  rw [knowable_iff_no_collision]
  constructor
  · intro hno i
    rw [ambiguity, Finset.card_le_one]
    rintro y hy z hz
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hz
    simp only [fibre, Finset.mem_filter] at hω hτ
    exact hno ω τ (hω.2.trans hτ.2.symm)
  · intro hle ω τ hobs
    have hmem : f ω ∈ ((fibre r (r ω)).image f) :=
      Finset.mem_image.mpr ⟨ω, by simp [fibre], rfl⟩
    have hmem' : f τ ∈ ((fibre r (r ω)).image f) :=
      Finset.mem_image.mpr ⟨τ, by simp [fibre, hobs], rfl⟩
    exact Finset.card_le_one.mp (hle (r ω)) _ hmem _ hmem'

/-- A single ambiguous observation value refutes exactness. -/
public theorem not_knowable_of_one_lt_ambiguity
    [Fintype Ω] [DecidableEq I] [DecidableEq Y] [Nonempty Y]
    {r : Ω → I} {f : Ω → Y} {i : I} (h : 1 < ambiguity r f i) :
    ¬ Knowable r f := by
  intro hk
  exact absurd ((knowable_iff_ambiguity_le_one r f).mp hk i) (Nat.not_le.mpr h)

/-! ## The counting obstruction -/

/--
**A channel cannot carry more than it has room for.** If the target is knowable
from the observation, the observation must take at least as many distinct values
as the target does.

This is not a collision statement — it never names a colliding pair. It says the
obstruction can be read off two cardinalities, which is what makes it usable
before any particular model is fixed.
-/
public theorem card_image_le_of_knowable
    [Fintype Ω] [DecidableEq I] [DecidableEq Y]
    {r : Ω → I} {f : Ω → Y} (h : Knowable r f) :
    (Finset.univ.image f).card ≤ (Finset.univ.image r).card := by
  obtain ⟨d, hd⟩ := h
  have himg : (Finset.univ.image f) = (Finset.univ.image r).image d := by
    rw [Finset.image_image]
    exact Finset.image_congr fun ω _ => hd ω
  rw [himg]
  exact Finset.card_image_le

/--
The contrapositive, and the form a consumer uses: a property with more values
than the observation has outcomes is **not** knowable from it.
-/
public theorem not_knowable_of_card_lt
    [Fintype Ω] [DecidableEq I] [DecidableEq Y]
    {r : Ω → I} {f : Ω → Y}
    (h : (Finset.univ.image r).card < (Finset.univ.image f).card) :
    ¬ Knowable r f :=
  fun hk => absurd (card_image_le_of_knowable hk) (Nat.not_le.mpr h)

/-! ## The worst case over all observation values -/

/-- An observation value nothing realizes leaves nothing open. -/
public theorem ambiguity_eq_zero_of_not_mem_image
    [Fintype Ω] [DecidableEq I] [DecidableEq Y]
    {r : Ω → I} {f : Ω → Y} {i : I} (h : i ∉ Finset.univ.image r) :
    ambiguity r f i = 0 := by
  have : fibre r i = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun ω hω => ?_
    simp only [fibre, Finset.mem_filter] at hω
    exact h (Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, hω.2⟩)
  simp [ambiguity, this]

/--
The **worst-case ambiguity**: the largest number of target values any single
observation value leaves open.

One scalar for a whole observation, where `ambiguity` is one number per
observation value. That is what a consumer ranking two observations needs, and
the empty fibres contribute `0` rather than distorting the maximum.
-/
@[expose] public def worstAmbiguity [Fintype Ω] [DecidableEq I] [DecidableEq Y]
    (r : Ω → I) (f : Ω → Y) : ℕ :=
  (Finset.univ.image r).sup (ambiguity r f)

/-- The worst case dominates every observation value, realized or not. -/
public theorem ambiguity_le_worstAmbiguity
    [Fintype Ω] [DecidableEq I] [DecidableEq Y]
    (r : Ω → I) (f : Ω → Y) (i : I) :
    ambiguity r f i ≤ worstAmbiguity r f := by
  by_cases h : i ∈ Finset.univ.image r
  · exact Finset.le_sup h
  · simp [ambiguity_eq_zero_of_not_mem_image h]

/--
Exactness is worst-case ambiguity at most one.

The scalar form of `knowable_iff_ambiguity_le_one`, and the statement a consumer
comparing two observations actually uses.
-/
public theorem knowable_iff_worstAmbiguity_le_one
    [Fintype Ω] [DecidableEq I] [DecidableEq Y] [Nonempty Y]
    (r : Ω → I) (f : Ω → Y) :
    Knowable r f ↔ worstAmbiguity r f ≤ 1 := by
  rw [knowable_iff_ambiguity_le_one]
  constructor
  · intro h
    exact Finset.sup_le fun i _ => h i
  · intro h i
    exact le_trans (ambiguity_le_worstAmbiguity r f i) h

/-! ## Ambiguity under coarsening -/

/--
**Post-processing never resolves anything.** Applying any function to an
observation's output can only merge fibres, so ambiguity at the merged value is
at least the ambiguity at the original.

`not_knowable_comp` says a failed decode stays failed. This says *how much* is
lost, and that it never goes down — the quantitative repair boundary.
-/
public theorem ambiguity_le_of_comp
    [Fintype Ω] [DecidableEq I] [DecidableEq Y] {K : Type*} [DecidableEq K]
    (r : Ω → I) (f : Ω → Y) (g : I → K) (i : I) :
    ambiguity r f i ≤ ambiguity (fun ω => g (r ω)) f (g i) := by
  refine Finset.card_le_card (Finset.image_subset_image ?_)
  intro ω hω
  simp only [fibre, Finset.mem_filter] at hω ⊢
  exact ⟨hω.1, by rw [hω.2]⟩

/--
**Coarsening never lowers the worst case either.** The scalar form of
`ambiguity_le_of_comp`: post-processing an observation can only move the maximum
up.

This is the quantitative repair boundary as a single comparable number, which is
what lets a consumer say one observation is strictly worse than another rather
than only that some fibre degraded.
-/
public theorem worstAmbiguity_le_of_comp
    [Fintype Ω] [DecidableEq I] [DecidableEq Y] {K : Type*} [DecidableEq K]
    (r : Ω → I) (f : Ω → Y) (g : I → K) :
    worstAmbiguity r f ≤ worstAmbiguity (fun ω => g (r ω)) f := by
  refine Finset.sup_le fun i _ => ?_
  exact le_trans (ambiguity_le_of_comp r f g i)
    (ambiguity_le_worstAmbiguity (fun ω => g (r ω)) f (g i))

end AISafetyAtlas.Knowledge
