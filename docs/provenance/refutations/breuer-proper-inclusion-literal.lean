import AISafetyAtlas.Examples.Knowledge.Embedded
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Breuer §3.4's "strictly more states" as printed is false; the finite form holds

Thomas Breuer, *The Impossibility of Accurate State Self-Measurements*, Philosophy of
Science 62 (1995) 197–214, §3.4 "A First Attempt", pp. 206–207 (PDF pp. 11–12; audit
row S19-R12):

    For exact measurability of all states it is necessary (but not sufficient) that
    there is a surjective map from the states of A onto the states of O. But if
    additionally A is a properly included in O, there are strictly more states of O
    than states of A. If O has only finitely many possible states, this already
    exludes the possibility of exact measurement of all states from inside the
    observed system.

(Transcribed from the page images, printed slips kept, in
`docs/provenance/printed-statements/breuer-1995-self-measurement.yaml`, entry
`br-finite-remark`.) The sentence at issue is the second. Its hypotheses are print's
§3.3 set-up: the restriction `s ↦ s|_A` is a surjective map from the states of `O`
to the states of `A` (`br-restriction-surjective`, p. 205), and proper inclusion is
the displayed assumption `(∃ s, s' ∈ 𝒮_O) : s|_A = s'|_A, s ≠ s'`
(`br-proper-inclusion`, p. 205). Both are the library's own definitions,
`AISafetyAtlas.Knowledge.Embedded.Restriction` and `ProperInclusion`. Print assumes
no finiteness for its general results (Setting, pp. 206–207), and the sentence sits
before the next sentence's "If `O` has only finitely many possible states".

Read literally, the sentence is false. The library's model `readNat`
(`AISafetyAtlas.Examples.Knowledge.Embedded`) has `O = ℕ × Bool`, `A = ℕ` and the
restriction `Prod.fst`, which is surjective and properly inclusive, while
`ℕ ≃ ℕ × Bool`: the two state sets have the same cardinality. The same model also
carries a surjection from the states of `A` onto the states of `O`, so the
refutation survives the reading in which "additionally" imports the previous
sentence's necessary condition as a further hypothesis
(`literal_false_with_measurement_surjection`).

**Modelling choice: "strictly more states".** Read as cardinality, `#A < #Ω`. At
finite sets it is `Fintype.card A < Fintype.card Ω`, the form the library proves.
Both state types live in `Type`; the counterexample lives there, so it refutes any
universe-polymorphic form, and the repair is stated there too.

Why the repair is the necessary one and not a different theorem:

* it adds one hypothesis, `[Finite Ω]`, and changes nothing else: `repaired_holds`
  is `LiteralPrint` with that binder added (finiteness of `A` is derived from the
  surjective restriction, not assumed);
* the hypothesis is print's own, the next sentence's "If `O` has only finitely many
  possible states", which is the one use print makes of the sentence;
* among conditions on `O`, it is sharp: at every infinite `O` the literal sentence
  fails (`literal_fails_at_every_infinite_system`), so no weaker condition on `O`
  alone repairs it.

It is not the weakest repair overall. Finiteness of `A` also suffices and is strictly
weaker (`holds_of_finite_apparatus`: at infinite `O` a finite `A` is trivially
smaller), and it is sharp among conditions on `A`
(`literal_fails_at_every_infinite_apparatus`). The file proves the repair the
author ruled on, and records the wider form without adopting it.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/breuer-proper-inclusion-literal.lean`.
Grading context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired
slips).
-/

open Cardinal
open AISafetyAtlas.Knowledge.Embedded
open AISafetyAtlas.Knowledge.Embedded.Finite
open AISafetyAtlas.Examples.Knowledge.Embedded

namespace BreuerProperInclusionLiteral

/-- The sentence exactly as printed, without finiteness: whenever the restriction of
`O`'s states to `A`'s is surjective (§3.3) and `A` is properly included in `O`, there
are strictly more states of `O` than of `A`. -/
def LiteralPrint : Prop :=
  ∀ (Ω A : Type) (restrict : Restriction Ω A),
    Function.Surjective restrict → ProperInclusion restrict → #A < #Ω

/-- At `readNat` the two state sets have the same cardinality, through the library's
`ℕ ≃ ℕ × Bool` (`readNat_footnote4`). -/
theorem readNat_card_eq : #ℕ = #(ℕ × Bool) := by
  obtain ⟨e⟩ := readNat_footnote4.1
  exact Cardinal.mk_congr e

/-- **The printed sentence is false.** `readNat` is surjective and properly inclusive,
yet `O = ℕ × Bool` has no more states than `A = ℕ`. -/
theorem literal_false : ¬ LiteralPrint := fun h =>
  (h (ℕ × Bool) ℕ readNat readNat_surjective readNat_properInclusion).ne readNat_card_eq

/-- The same witness refutes the reading in which "additionally" also assumes the
previous sentence's surjection from the states of `A` onto the states of `O`. -/
theorem literal_false_with_measurement_surjection :
    ¬ ∀ (Ω A : Type) (restrict : Restriction Ω A),
      Function.Surjective restrict → ProperInclusion restrict →
      (∃ f : A → Ω, Function.Surjective f) → #A < #Ω := fun h =>
  (h (ℕ × Bool) ℕ readNat readNat_surjective readNat_properInclusion
    readNat_surjection_not_sufficient.1).ne readNat_card_eq

/-- **The sentence read inside the finite remark holds**: `LiteralPrint` with
`[Finite Ω]` added, by the library's `card_lt_of_properInclusion`. -/
theorem repaired_holds :
    ∀ (Ω A : Type) [Finite Ω] (restrict : Restriction Ω A),
      Function.Surjective restrict → ProperInclusion restrict → #A < #Ω := by
  intro Ω A _ restrict hsurj hp
  have : Finite A := Finite.of_surjective restrict hsurj
  have := Fintype.ofFinite Ω
  have := Fintype.ofFinite A
  rw [Cardinal.mk_fintype, Cardinal.mk_fintype]
  exact_mod_cast card_lt_of_properInclusion restrict hsurj hp

/-- An infinite state set is as large as two copies of itself. -/
theorem mk_prod_bool_of_infinite (X : Type) [Infinite X] : #(X × Bool) = #X := by
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_fintype Bool,
    Fintype.card_bool]
  exact Cardinal.mul_eq_left (Cardinal.aleph0_le_mk X)
    ((Cardinal.natCast_lt_aleph0 (n := 2)).le.trans (Cardinal.aleph0_le_mk X))
    (Nat.cast_ne_zero.2 (by decide))

/-- **Sharp among conditions on `O`**: at every infinite state set of `O` the literal
sentence fails, for `A = O` read through `O ≃ O × Bool` with the bit beyond reach. -/
theorem literal_fails_at_every_infinite_system (Ω : Type) [Infinite Ω] :
    ∃ (A : Type) (restrict : Restriction Ω A),
      Function.Surjective restrict ∧ ProperInclusion restrict ∧ ¬ #A < #Ω := by
  obtain ⟨e⟩ := Cardinal.eq.1 (mk_prod_bool_of_infinite Ω)
  obtain ⟨a⟩ := (inferInstance : Nonempty Ω)
  refine ⟨Ω, fun s => (e.symm s).1, fun x => ⟨e (x, false), by simp⟩,
    ⟨e (a, false), e (a, true), by simp, fun h => ?_⟩, lt_irrefl _⟩
  simpa using e.injective h

/-- **Sharp among conditions on `A`**: at every infinite state set of `A` the literal
sentence fails, for `O = A × Bool` restricted by `Prod.fst`. -/
theorem literal_fails_at_every_infinite_apparatus (A : Type) [Infinite A] :
    ∃ (Ω : Type) (restrict : Restriction Ω A),
      Function.Surjective restrict ∧ ProperInclusion restrict ∧ ¬ #A < #Ω := by
  obtain ⟨a⟩ := (inferInstance : Nonempty A)
  refine ⟨A × Bool, Prod.fst, fun x => ⟨(x, false), rfl⟩,
    ⟨(a, false), (a, true), rfl, by simp⟩, ?_⟩
  rw [mk_prod_bool_of_infinite A]
  exact lt_irrefl _

/-- **The wider repair, recorded and not adopted**: finiteness of `A` alone suffices.
It is implied by `[Finite Ω]` through the surjective restriction, and strictly weaker:
at infinite `O` a finite `A` is smaller outright. -/
theorem holds_of_finite_apparatus :
    ∀ (Ω A : Type) [Finite A] (restrict : Restriction Ω A),
      Function.Surjective restrict → ProperInclusion restrict → #A < #Ω := by
  intro Ω A _ restrict hsurj hp
  rcases finite_or_infinite Ω with hΩ | hΩ
  · exact repaired_holds Ω A restrict hsurj hp
  · exact (Cardinal.lt_aleph0_of_finite A).trans_le (Cardinal.aleph0_le_mk Ω)

end BreuerProperInclusionLiteral
