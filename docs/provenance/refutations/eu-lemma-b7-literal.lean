import AISafetyAtlas.Sovereignty.EUDetermined
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Turner–Tadepalli Lemma B.7 as printed is false; the repaired lemma is the one that holds

Alexander Matt Turner and Prasad Tadepalli, *Parametrically Retargetable
Decision-Makers Tend To Seek Power*, arXiv:2206.13477v2 (2022), Appendix B, Lemma B.7
(Quantitative general orbit lemma), PDF pp. 18-19 (audit row S16-R09). The opening
and item 1 are at the foot of p. 18; items 2-4 and the conclusion are on p. 19:

    Let Θ be a subset of a set acted on by S_d, and let f : E × Θ → ℝ. Consider
    A, B ∈ E.
    For each θ ∈ Θ, choose involutions φ_1, …, φ_n ∈ S_d. Let θ* ∈ Orbit|_Θ(θ).
    1. Retargetable under parameter permutation. There exist B*_i ∈ E such that if
       f(B | θ*) < f(A | θ*), then ∀ i : f(A | θ*) ≤ f(B*_i | φ_i · θ*).
    2. Θ is closed under certain symmetries. f(B | θ*) < f(A | θ*) ⟹
       ∀ i : φ_i · θ* ∈ Θ.
    3. f is increasing on certain inputs. ∀ i : f(B*_i | θ*) ≤ f(B | θ*).
    4. Increasing under alternate symmetries. For j = 1, …, n and i ≠ j, if
       f(A | θ*) < f(B | θ*), then f(B*_j | θ*) ≤ f(B*_j | φ_i · θ*).
    If these conditions hold for all θ ∈ Θ, then
       f(B | θ) ≥ⁿ_{most: Θ} f(A | θ).                                    (23)

(Transcribed from the page images in
`docs/provenance/printed-statements/turner-tadepalli-2022-retargetable.yaml`, entry
`tt-lemma-B.7`.) `≥ⁿ_{most: Θ}` is Definition 3.2 (p. 4, with `n ≥ 1`), which the
library renders as `AISafetyAtlas.Sovereignty.MostOrbit`; `Orbit|_Θ(θ)` is
Definition 3.1, rendered as `orbitIn`.

## The reading refuted here

`LiteralPrint` takes the quantifiers in the order the text gives them: for each `θ`
the involutions are chosen; then `θ*` is fixed; then item 1 says *there exist*
`B*_i`, which items 3 and 4 reuse. So the `B*_i` are chosen per `θ*`, and item 1
keeps its guard `f(B | θ*) < f(A | θ*)`. The page also admits a second reading of
the `B*_i`: chosen once per `θ`, together with the `φ_i`. That reading, with item 1
unguarded, is the library's `AISafetyAtlas.Sovereignty.mostOrbit_of_orbitConditions`,
and it is what print's own proof (p. 19) uses:

* equation (25) applies item 1 at `φ_i⁻¹ · θ*`, where the guard would read
  `f(B | φ_i · θ*) < f(A | φ_i · θ*)`, the negation of what (29) concludes;
* the disjointness chain (30)-(33) reads the same `B*_j` at `θ''`, at `φ_i · θ'` and
  at `θ'`, three different orbit points.

This file proves that the literal reading is false, and that each of the two
changes is separately necessary:

* `not_guardedUniform`: keep the guard, choose the `B*_i` per `θ` (the second
  reading of the page): false, by witness 1;
* `not_unguardedPerPoint`: drop the guard, choose the `B*_i` per `θ*`: false, by
  witness 2;
* `not_literalPrint`: the literal reading implies both, so it is false.

Both witnesses live on `Ω = Θ = {0, 1}` with `S_2` acting by the transposition,
`n = 1` and `φ_1` the transposition; item 4 is vacuous at `n = 1`. Since `Θ = Ω`,
the extension of `f` from `E × Θ` to `E × Ω` (needed to state items 1 and 4 when
`φ_i · θ*` leaves `Θ`) plays no role in either witness. In both, `B` beats `A`
nowhere and `A` beats `B` at `0`, so at `θ = 0` the `B`-favouring part of the orbit
is empty and the `A`-favouring part is not: (23) reads `0 ≥ 1 · 1` for witness 1 and
`0 ≥ 1 · 2` for witness 2.

Why the repair is the necessary one and not a different theorem:

* it changes exactly the two places where the proof uses more than the statement
  gives, and nothing else: items 2-4 keep print's form and guards, because the
  proof applies them only where their guards hold (item 4 at (32), at
  `φ_i⁻¹ · θ' = φ_i · θ'`, which lies in `Orbit|_{Θ,B>A}(θ)` "by the first half of
  this proof");
* print's table 3 (p. 18) shows that item 4 itself is needed, so the repair cannot
  drop it;
* Lemma B.9 (p. 20), which applies B.7, checks item 1 with no guard ("Holds since
  f(A | θ*) ≤ f(φ_i · A | φ_i · θ*) ≤ f(B*_i | φ_i · θ*)"), and its `B*_i` are the
  superset copies its hypothesis fixes (Definition B.8), not chosen per `θ*`; so
  nothing downstream is lost. (Proposition 3.4's closing "apply lemma B.7" reads as
  a slip for Theorem 3.6; see the yaml note on `tt-prop-3.4`.)
* the repaired lemma holds for every `d`, `Θ`, `E`, `f`, `A`, `B`, `n`
  (`repaired_holds`), and its hypotheses are inhabited non-vacuously
  (`repaired_inhabited`).

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/eu-lemma-b7-literal.lean`. Grading
context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired slips);
final grade: id 180 in `docs/provenance/regrade-2026-11/final-grades.tsv`.
-/

open AISafetyAtlas.Sovereignty

namespace TurnerTadepalliLemmaBSevenLiteral

/-- Items 1-4 of Lemma B.7 at one orbit point `θs`, as printed: items 1 and 2 are
guarded by `f(B | θs) < f(A | θs)`, item 4 by `f(A | θs) < f(B | θs)`. -/
def Items {G Ω E : Type} [Group G] [MulAction G Ω] {n : ℕ} (Θ : Set Ω)
    (f : E → Ω → ℝ) (A B : E) (φ : Fin n → G) (Bstar : Fin n → E) (θs : Ω) : Prop :=
  (f B θs < f A θs → ∀ i, f A θs ≤ f (Bstar i) (φ i • θs)) ∧
  (f B θs < f A θs → ∀ i, φ i • θs ∈ Θ) ∧
  (∀ i, f (Bstar i) θs ≤ f B θs) ∧
  (∀ j i, i ≠ j → f A θs < f B θs → f (Bstar j) θs ≤ f (Bstar j) (φ i • θs))

/-- Items 1-4 with item 1 unguarded, as the library states them. -/
def ItemsUnguarded {G Ω E : Type} [Group G] [MulAction G Ω] {n : ℕ} (Θ : Set Ω)
    (f : E → Ω → ℝ) (A B : E) (φ : Fin n → G) (Bstar : Fin n → E) (θs : Ω) : Prop :=
  (∀ i, f A θs ≤ f (Bstar i) (φ i • θs)) ∧
  (f B θs < f A θs → ∀ i, φ i • θs ∈ Θ) ∧
  (∀ i, f (Bstar i) θs ≤ f B θs) ∧
  (∀ j i, i ≠ j → f A θs < f B θs → f (Bstar j) θs ≤ f (Bstar j) (φ i • θs))

/-- Lemma B.7 exactly as printed, in the text's quantifier order: `S_d` acts on a
set `Ω ⊇ Θ`; for each `θ ∈ Θ` involutions `φ_1, …, φ_n` are chosen; for each `θ*`
in `θ`'s orbit inside `Θ` there exist `B*_i` meeting items 1-4 (item 1 guarded);
then (23), with `n ≥ 1` from Definition 3.2. -/
def LiteralPrint : Prop :=
  ∀ (d : ℕ) (Ω : Type) [MulAction (Equiv.Perm (Fin d)) Ω] (Θ : Set Ω)
    (E : Type) (f : E → Ω → ℝ) (A B : E) (n : ℕ), 1 ≤ n →
    (∀ θ ∈ Θ, ∃ φ : Fin n → Equiv.Perm (Fin d), (∀ i, φ i * φ i = 1) ∧
      ∀ θs ∈ orbitIn (Equiv.Perm (Fin d)) Θ θ, ∃ Bstar : Fin n → E,
        Items Θ f A B φ Bstar θs) →
    MostOrbit (Equiv.Perm (Fin d)) n Θ (f A) (f B)

/-- The second reading of the page with the guard kept: the `B*_i` are chosen per
`θ`, together with the `φ_i`. -/
def GuardedUniform : Prop :=
  ∀ (d : ℕ) (Ω : Type) [MulAction (Equiv.Perm (Fin d)) Ω] (Θ : Set Ω)
    (E : Type) (f : E → Ω → ℝ) (A B : E) (n : ℕ), 1 ≤ n →
    (∀ θ ∈ Θ, ∃ φ : Fin n → Equiv.Perm (Fin d), ∃ Bstar : Fin n → E,
      (∀ i, φ i * φ i = 1) ∧
      ∀ θs ∈ orbitIn (Equiv.Perm (Fin d)) Θ θ, Items Θ f A B φ Bstar θs) →
    MostOrbit (Equiv.Perm (Fin d)) n Θ (f A) (f B)

/-- The literal quantifier order with item 1 unguarded: the `B*_i` still vary with
`θ*`. -/
def UnguardedPerPoint : Prop :=
  ∀ (d : ℕ) (Ω : Type) [MulAction (Equiv.Perm (Fin d)) Ω] (Θ : Set Ω)
    (E : Type) (f : E → Ω → ℝ) (A B : E) (n : ℕ), 1 ≤ n →
    (∀ θ ∈ Θ, ∃ φ : Fin n → Equiv.Perm (Fin d), (∀ i, φ i * φ i = 1) ∧
      ∀ θs ∈ orbitIn (Equiv.Perm (Fin d)) Θ θ, ∃ Bstar : Fin n → E,
        ItemsUnguarded Θ f A B φ Bstar θs) →
    MostOrbit (Equiv.Perm (Fin d)) n Θ (f A) (f B)

/-- The repaired lemma, the library's hypotheses at `S_d`: item 1 unguarded, the
`B*_i` chosen per `θ` with the `φ_i`. (`n ≥ 1` is not needed.) -/
def Repaired : Prop :=
  ∀ (d : ℕ) (Ω : Type) [MulAction (Equiv.Perm (Fin d)) Ω] (Θ : Set Ω)
    (E : Type) (f : E → Ω → ℝ) (A B : E) (n : ℕ),
    (∀ θ ∈ Θ, ∃ φ : Fin n → Equiv.Perm (Fin d), ∃ Bstar : Fin n → E,
      (∀ i, φ i * φ i = 1) ∧
      ∀ θs ∈ orbitIn (Equiv.Perm (Fin d)) Θ θ, ItemsUnguarded Θ f A B φ Bstar θs) →
    MostOrbit (Equiv.Perm (Fin d)) n Θ (f A) (f B)

/-- The literal reading has the weakest hypotheses, so it implies the reading with
uniform `B*_i`. -/
theorem LiteralPrint.guardedUniform (h : LiteralPrint) : GuardedUniform := by
  intro d Ω _ Θ E f A B n hn hyp
  refine h d Ω Θ E f A B n hn fun θ hθ => ?_
  obtain ⟨φ, Bstar, hinv, hit⟩ := hyp θ hθ
  exact ⟨φ, hinv, fun θs hθs => ⟨Bstar, hit θs hθs⟩⟩

/-- The literal reading implies the reading with item 1 unguarded. -/
theorem LiteralPrint.unguardedPerPoint (h : LiteralPrint) : UnguardedPerPoint := by
  intro d Ω _ Θ E f A B n hn hyp
  refine h d Ω Θ E f A B n hn fun θ hθ => ?_
  obtain ⟨φ, hinv, hall⟩ := hyp θ hθ
  refine ⟨φ, hinv, fun θs hθs => ?_⟩
  obtain ⟨Bstar, h1, h2, h3, h4⟩ := hall θs hθs
  exact ⟨Bstar, fun _ => h1, h2, h3, h4⟩

/-! ## The common setting of both witnesses -/

/-- The transposition of the two parameters, the non-identity element of `S_2`. -/
def swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

theorem swap_involutive : swap * swap = 1 := Equiv.swap_mul_self 0 1

theorem swap_zero : swap 0 = 1 := rfl

theorem swap_one : swap 1 = 0 := rfl

/-- (23) fails at `θ = 0` on `Ω = Θ = Fin 2` whenever `B` beats `A` nowhere and `A`
beats `B` at `0`: no orbit point favours `B`, and at least `0` favours `A`. -/
theorem not_mostOrbit {n : ℕ} (hn : 1 ≤ n) (fA fB : Fin 2 → ℝ) (hle : ∀ t, fB t ≤ fA t)
    (h0 : fB 0 < fA 0) : ¬ MostOrbit (Equiv.Perm (Fin 2)) n Set.univ fA fB := by
  intro h
  have hfav : orbitFavouring (Equiv.Perm (Fin 2)) Set.univ fA fB 0 = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun t ht => (hle t).not_gt ht.2
  have hag : 0 < (orbitAgainst (Equiv.Perm (Fin 2)) Set.univ fA fB 0).ncard :=
    (Set.ncard_pos).2 ⟨0, ⟨MulAction.mem_orbit_self 0, Set.mem_univ 0⟩, h0⟩
  have := h 0 (Set.mem_univ 0)
  rw [hfav, Set.ncard_empty] at this
  have := Nat.mul_pos hn hag
  omega

/-! ## Witness 1: the guard of item 1 is fatal

`E = {A, B}` with `A = 0`, `B = 1`; `f(A | ·) = (1, 1)`, `f(B | ·) = (0, 1)`;
`B*_1 = B` at every point. -/

/-- Witness 1's objective: row `e` is `f(e | ·)`. -/
def f₁ : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![0, 1]]

/-- Items 1-4 as printed (guarded item 1) hold at both orbit points with the same
`B*_1 = B`: at `0`, `f(A | 0) = 1 ≤ f(B | 1) = 1`; at `1` the guard `1 < 1` fails. -/
theorem items₁ (θs : Fin 2) :
    Items Set.univ f₁ 0 1 (fun _ : Fin 1 => swap) (fun _ => 1) θs := by
  refine ⟨fun hlt _ => ?_, fun _ _ => Set.mem_univ _, fun _ => le_rfl,
    fun j i hij _ => absurd (Subsingleton.elim i j) hij⟩
  fin_cases θs
  · simp [f₁, swap_zero]
  · simp [f₁] at hlt

theorem le₁ (t : Fin 2) : f₁ 1 t ≤ f₁ 0 t := by
  fin_cases t <;> simp [f₁]

theorem lt₁ : f₁ 1 0 < f₁ 0 0 := by simp [f₁]

/-- **Keeping the guard is fatal**, even with the `B*_i` chosen per `θ`. -/
theorem not_guardedUniform : ¬ GuardedUniform := fun h =>
  not_mostOrbit le_rfl (f₁ 0) (f₁ 1) le₁ lt₁
    (h 2 (Fin 2) Set.univ (Fin 2) f₁ 0 1 1 le_rfl fun _ _ =>
      ⟨fun _ => swap, fun _ => 1, fun _ => swap_involutive, fun θs _ => items₁ θs⟩)

/-! ## Witness 2: choosing `B*_i` per orbit point is fatal

`E = {A, B, B₁, B₂}`; `f(A | ·) = (1, 1)`, `f(B | ·) = (0, 0)`, `f(B₁ | ·) = (0, 1)`, `f(B₂ | ·) = (5, 0)`;
`B*_1 = B₁` at `0` and `B*_1 = B₂` at `1`. -/

/-- Witness 2's option sets. -/
inductive Opt
  | A | B | B₁ | B₂

/-- Witness 2's objective. -/
def f₂ : Opt → Fin 2 → ℝ
  | .A => ![1, 1]
  | .B => ![0, 0]
  | .B₁ => ![0, 1]
  | .B₂ => ![5, 0]

/-- Witness 2's choice of `B*_1` at each orbit point. -/
def bstar₂ : Fin 2 → Opt := ![.B₁, .B₂]

/-- Items 1-4 with item 1 unguarded hold at both points, with `B*_1` varying:
at `0`, `1 ≤ f(B₁ | 1) = 1` and `f(B₁ | 0) = 0 ≤ f(B | 0) = 0`; at `1`,
`1 ≤ f(B₂ | 0) = 5` and `f(B₂ | 1) = 0 ≤ f(B | 1) = 0`. -/
theorem items₂ (θs : Fin 2) :
    ItemsUnguarded Set.univ f₂ .A .B (fun _ : Fin 1 => swap) (fun _ => bstar₂ θs) θs := by
  refine ⟨fun _ => ?_, fun _ _ => Set.mem_univ _, fun _ => ?_,
    fun j i hij _ => absurd (Subsingleton.elim i j) hij⟩ <;>
  fin_cases θs <;> norm_num [f₂, bstar₂, swap_zero, swap_one]

theorem le₂ (t : Fin 2) : f₂ .B t ≤ f₂ .A t := by
  fin_cases t <;> simp [f₂]

theorem lt₂ : f₂ .B 0 < f₂ .A 0 := by simp [f₂]

/-- **Choosing the `B*_i` per orbit point is fatal**, even with item 1 unguarded. -/
theorem not_unguardedPerPoint : ¬ UnguardedPerPoint := fun h =>
  not_mostOrbit le_rfl (f₂ .A) (f₂ .B) le₂ lt₂
    (h 2 (Fin 2) Set.univ Opt f₂ .A .B 1 le_rfl fun _ _ =>
      ⟨fun _ => swap, fun _ => swap_involutive,
        fun θs _ => ⟨fun _ => bstar₂ θs, items₂ θs⟩⟩)

/-! ## The verdict -/

/-- **Lemma B.7 as printed is false.** Witness 1 meets the literal hypotheses with
`B*_1 = B` at both points; witness 2 refutes it as well
(`LiteralPrint.unguardedPerPoint` and `not_unguardedPerPoint`). -/
theorem not_literalPrint : ¬ LiteralPrint := fun h =>
  not_guardedUniform h.guardedUniform

/-- **The repaired lemma holds**, for every `d`, `Ω`, `Θ`, `E`, `f`, `A`, `B`, `n`:
it is the library's `mostOrbit_of_orbitConditions` at `G = S_d`. -/
theorem repaired_holds : Repaired := by
  intro d Ω _ Θ E f A B n hyp
  refine mostOrbit_of_orbitConditions fun θ hθ => ?_
  obtain ⟨φ, Bstar, hinv, hit⟩ := hyp θ hθ
  exact ⟨φ, Bstar, hinv, fun θs h => (hit θs h).1, fun θs h => (hit θs h).2.1,
    fun θs h => (hit θs h).2.2.1, fun θs h hlt i j hij => (hit θs h).2.2.2 j i hij hlt⟩

/-- Repaired witness: `f(A | ·) = (1, 0)`, `f(B | ·) = (0, 1)`. -/
def f₀ : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

/-- **The repaired hypotheses are inhabited, and not vacuously**: on the same
setting, with `B*_1 = B` and `φ_1` the transposition, the unguarded items hold, `A`
beats `B` at `0` (so (23) has an `A`-favouring point to account for), and (23)
holds. -/
theorem repaired_inhabited :
    (∀ θs : Fin 2,
      ItemsUnguarded Set.univ f₀ 0 1 (fun _ : Fin 1 => swap) (fun _ => 1) θs) ∧
    (0 : Fin 2) ∈ orbitAgainst (Equiv.Perm (Fin 2)) Set.univ (f₀ 0) (f₀ 1) 0 ∧
    MostOrbit (Equiv.Perm (Fin 2)) 1 Set.univ (f₀ 0) (f₀ 1) := by
  have hit : ∀ θs : Fin 2,
      ItemsUnguarded Set.univ f₀ 0 1 (fun _ : Fin 1 => swap) (fun _ => 1) θs := by
    intro θs
    refine ⟨fun _ => ?_, fun _ _ => Set.mem_univ _, fun _ => le_rfl,
      fun j i hij _ => absurd (Subsingleton.elim i j) hij⟩
    fin_cases θs <;> simp [f₀, swap_zero, swap_one]
  refine ⟨hit, ⟨⟨MulAction.mem_orbit_self 0, Set.mem_univ 0⟩, by simp [f₀]⟩,
    repaired_holds 2 (Fin 2) Set.univ (Fin 2) f₀ 0 1 1 fun _ _ =>
      ⟨fun _ => swap, fun _ => 1, fun _ => swap_involutive, fun θs _ => hit θs⟩⟩

end TurnerTadepalliLemmaBSevenLiteral
