import AISafetyAtlas.Control.RequisiteVariety

/-!
# Ashby 11/8's minimum is not attained by a table outcome; it is attained over §11/8's own E

W. Ross Ashby, *An Introduction to Cybernetics* (1956; second impression 1957), §11/8,
book p. 208 (PDF p. 111; audit row S03-R07):

    Thus the entropy of the E's has a certain minimum. If this minimum is
    to be affected by a relation between the D- and R-sources, it can be made
    least when H_D(R) = 0, i.e. when R is a determinate function of D.
    When this is so, then H(E)'s minimum is H(D) − H(R), a deduction
    similar to that of the previous section.

(Transcribed from the page image in
`docs/provenance/printed-statements/ashby-1957-introduction-to-cybernetics.yaml`,
entry `ashby-11-8-determinate`.) The bound it refers to is §11/8's last display,
repaired to `H(E) ≥ H(D) + H_D(R) − H(R)`
(`docs/provenance/refutations/ashby-11-8-display-literal.lean`), under §11/8's
premise `H_R(E) ≥ H_R(D)` (entry `ashby-11-8-hyp`, p. 207). As in §11/7, whose
identical idiom the yaml note on `ashby-11-7` reads as *asserting attainment as
well as the bound*, "minimum" asserts that some `E` reaches `H(D) − H(R)`.

**The literal reading.** "A deduction similar to that of the previous section"
invites reading `E` as the outcome of a §11/5 table: `E = T(D, R)` with no
repeated outcome in a column. Fix the disturbance and the determinate response
`R = ρ(D)`. The reading says some such table attains `H(E) = H(D) − H(R)`. It is
false. Take `D` uniform on three values and `ρ` splitting them into blocks
`{0, 1}` and `{2}`. Under the column condition `H_R(E) = H_R(D)`
(`AISafetyAtlas.Control.condEntropy_outcome_eq`) and, with `H_D(R) = 0`,
`H(D) − H(R) = H_R(D)`. So attainment means `H(E) = H_R(E)`, i.e. `E` independent
of `R`. Given `R` on the singleton block, `E = T(2, ρ 2)` is a single value `c`,
so independence forces `P(E = c) = 1`. That makes `T(0, r₀) = T(1, r₀)` for the
response `r₀` of the other block, contradicting the column condition.
`no_table_attains` proves this for every column-injective table into every
outcome type, and `table_outcome_gt` that the bound is strict. Numerically
`H(E) ≥ H(1/3, 2/3) ≈ 0.918` bits against `H(D) − H(R) = 2/3` bits (not proved
here; the proof needs only `H(D) − H(R) > 0`).

Another reading is trivially true, so it is not used. Fix the table and let the
regulator vary, as `docs/provenance/refutations/ashby-11-7-literal.lean` does for
§11/7. A constant `ρ` has `H(R) = 0`, and with injective columns
`H(E) = H(D) = H(D) − H(R)`, so "some regulator attains its own bound" always
holds (not proved here). The bound depends on `ρ` through `H(R)`, so "minimum" is over `E` with
`(D, R)` fixed.

**The repair.** Over §11/8's own variables the minimum is attained. These are
*"three variables [...] Without any regard for how they are related causally"*
(p. 207), constrained only by the premise `H_R(E) ≥ H_R(D)`. For every `D`, `R`
with `H_D(R) = 0` there is an `E` meeting the premise with `H(E) = H(D) − H(R)`:
`E` independent of `R`, with entropy exactly `H_R(D)`. That is
`AISafetyAtlas.Control.exists_entropy_eq_sub_of_condEntropy_eq_zero`, and
`repaired_holds` pairs it with the bound
`AISafetyAtlas.Control.entropy_ge_sub_of_condEntropy_eq_zero`.

Why the repair is the necessary one and minimal:

* necessary: `literal_false` shows the table-outcome reading fails at a `(D, ρ)`
  that meets every hypothesis print states;
* it keeps the value `H(D) − H(R)`, the hypothesis `H_D(R) = 0` and the
  attainment. Dropping the attainment, as the §11/7 repair had to, would weaken
  print further than needed, because here attainment survives;
* the one change is the class `E` ranges over, from §11/5 table outcomes to
  §11/8's premise class. That is the class §11/8 itself states, and the class
  over which the bound is proved, so the minimum and the bound refer to the same
  set of `E`.

Modelling choice a reader may dispute: the attaining `E` lives on an extension
`Ω × Fin (n + 1)` carrying a copy of `(D, R)` with the same joint law (stated as
`IdentDistrib`), not on the original sample space. On the original space it need
not exist: on the witness space no variable meeting the premise attains the bound,
table outcome or not (`no_attaining_on_three`).
Ashby's "sources" are distributions, and §11/8 measures them *"empirically"*, so
the copy is the same pair of sources.

Units: PFR's entropies are in nats; every statement here is homogeneous in the
logarithm.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/ashby-11-8-minimum-literal.lean`.
Grading context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired
slips); final grade: id 198 in
`docs/provenance/regrade-2026-11/final-grades.tsv`.
-/

open MeasureTheory ProbabilityTheory AISafetyAtlas.Control

namespace AshbyElevenEightMinimumLiteral

/-- §11/8's minimum read over §11/5 table outcomes. For every finite disturbance
alphabet, law of `D` and determinate response `R = ρ(D)`, every table with no
repeated outcome in a column gives `H(E) ≥ H(D) − H(R)`, and some such table
attains `H(E) = H(D) − H(R)`. -/
def LiteralPrint : Prop :=
  ∀ (Ω D R : Type) [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace R]
    [MeasurableSingletonClass D] [MeasurableSingletonClass R] [Finite D] [Finite R]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Dv : Ω → D) (ρ : D → R),
    Measurable Dv → Measurable ρ →
    (∀ (E : Type) [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
        (T : D → R → E), Measurable (fun p : D × R => T p.1 p.2) →
        (∀ r : R, Function.Injective fun d => T d r) →
        H[Dv ; μ] - H[ρ ∘ Dv ; μ] ≤ H[(fun ω => T (Dv ω) (ρ (Dv ω))) ; μ]) ∧
    ∃ (E : Type) (_ : MeasurableSpace E) (_ : MeasurableSingletonClass E) (_ : Countable E)
      (T : D → R → E), Measurable (fun p : D × R => T p.1 p.2) ∧
      (∀ r : R, Function.Injective fun d => T d r) ∧
      H[(fun ω => T (Dv ω) (ρ (Dv ω))) ; μ] = H[Dv ; μ] - H[ρ ∘ Dv ; μ]

/-- Three equally likely disturbances. -/
noncomputable def three : Measure (Fin 3) := uniformOn Set.univ

instance : IsProbabilityMeasure three := by unfold three; infer_instance

/-- The determinate response: blocks `{0, 1}` (`false`) and `{2}` (`true`). -/
def split : Fin 3 → Bool := fun d => decide (d = 2)

theorem three_singleton_ne_zero (x : Fin 3) : three {x} ≠ 0 := by
  rw [three, uniformOn_univ]; simp

/-- Print's minimum at this `(D, ρ)` is positive: `H(D) = log 3` and `H(R) ≤ log 2`. -/
theorem bound_pos : 0 < H[(id : Fin 3 → Fin 3) ; three] - H[split ∘ id ; three] := by
  have h3 : H[(id : Fin 3 → Fin 3) ; three] = Real.log 3 := by
    rw [three, IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
    simp [Set.ncard_univ]
  have h2 : H[split ∘ id ; three] ≤ Real.log 2 := by
    simpa using entropy_le_log_card (split ∘ id) three
  have : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- **On this sample space no variable attains `H(D) − H(R)`**, table outcome or
not. If `E` meets §11/8's premise and attains, then
`H(E) ≥ H_R(E) ≥ H_R(D) = H(D) − H(R) = H(E)`, so `E` is independent of `R`. Given
`R` on the singleton block, `E = E(2)`; independence then puts all the mass on
`E(2)`, and every point has mass, so `E` is constant and `H(E) = 0 < H(D) − H(R)`.
This is why the attaining `E` of the repair lives on an extension. -/
theorem no_attaining_on_three {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [Countable E] (Ev : Fin 3 → E)
    (hkey : H[(id : Fin 3 → Fin 3) | split ∘ id ; three] ≤ H[Ev | split ∘ id ; three]) :
    H[Ev ; three] ≠ H[(id : Fin 3 → Fin 3) ; three] - H[split ∘ id ; three] := by
  intro hEq
  have hD : Measurable (id : Fin 3 → Fin 3) := measurable_id
  have hR : Measurable (split ∘ id) := .of_discrete
  have hE : Measurable Ev := .of_discrete
  have : FiniteRange Ev := ⟨Set.toFinite _⟩
  have : FiniteRange (split ∘ id) := ⟨Set.toFinite _⟩
  have : FiniteRange (id : Fin 3 → Fin 3) := ⟨Set.toFinite _⟩
  -- determinacy gives `H_R(D) = H(D) − H(R)`, so `H(E) ≥ H_R(E) ≥ H_R(D) = H(E)`
  have hdet : H[split ∘ id | (id : Fin 3 → Fin 3) ; three] = 0 :=
    AISafetyAtlas.InformationTheory.condEntropy_comp_self_left three hD .of_discrete
  have h₁ := chain_rule three hD hR
  have h₂ := chain_rule three hR hD
  have h₃ := entropy_comm hD hR three
  have h₄ : H[Ev | split ∘ id ; three] ≤ H[Ev ; three] := condEntropy_le_entropy three hE hR
  -- so `I[E : R] = 0`, i.e. independence
  have hI : I[Ev : split ∘ id ; three] = 0 := by
    rw [mutualInfo_eq_entropy_sub_condEntropy hE hR]
    linarith
  have hind : IndepFun Ev (split ∘ id) three := (mutualInfo_eq_zero hE hR).mp hI
  -- the singleton block `{2}` lies inside the fibre of `E` at `E 2`
  set c := Ev 2
  have hsub : (split ∘ id) ⁻¹' {true} ⊆ Ev ⁻¹' {c} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply, id, split,
      decide_eq_true_eq] at hx
    subst hx
    rfl
  have hmul := hind.measure_inter_preimage_eq_mul {c} {true} (measurableSet_singleton _)
    (measurableSet_singleton _)
  rw [Set.inter_eq_right.mpr hsub] at hmul
  have hB : (split ∘ id) ⁻¹' {true} = {2} := by
    ext x; fin_cases x <;> simp [split]
  rw [hB] at hmul
  -- independence puts all the mass on `c`, and every point has mass, so `E` is constant
  have hA : three (Ev ⁻¹' {c}) = 1 :=
    (ENNReal.mul_eq_right (three_singleton_ne_zero 2) (measure_ne_top _ _)).mp hmul.symm
  have hAc : three (Ev ⁻¹' {c})ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff (measurableSet_singleton _ |>.preimage hE)]; exact hA
  have hconst : Ev = fun _ => c := by
    funext x
    by_contra hx
    exact three_singleton_ne_zero x (measure_mono_null (by simpa using hx) hAc)
  -- then `H(E) = 0 < H(D) − H(R)`
  rw [hconst, entropy_const] at hEq
  linarith [bound_pos]

/-- **No column-injective table attains `H(D) − H(R)`** at this `(D, ρ)`, whatever
the outcome type: the table outcome meets §11/8's premise, with equality
(`AISafetyAtlas.Control.condEntropy_outcome_eq`), so `no_attaining_on_three`
applies. -/
theorem no_table_attains {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [Countable E] (T : Fin 3 → Bool → E)
    (hcol : ∀ r : Bool, Function.Injective fun d => T d r) :
    H[(fun ω => T (id ω) (split (id ω))) ; three]
      ≠ H[(id : Fin 3 → Fin 3) ; three] - H[split ∘ id ; three] :=
  no_attaining_on_three _
    (condEntropy_outcome_eq three measurable_id (.of_discrete : Measurable (split ∘ id)) T
      hcol).ge

/-- **The bound is strict at this `(D, ρ)`** for every column-injective table:
the library's `entropy_outcome_ge_of_strategy` and `no_table_attains`. -/
theorem table_outcome_gt {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [Countable E] (T : Fin 3 → Bool → E)
    (hcol : ∀ r : Bool, Function.Injective fun d => T d r) :
    H[(id : Fin 3 → Fin 3) ; three] - H[split ∘ id ; three]
      < H[(fun ω => T (id ω) (split (id ω))) ; three] :=
  lt_of_le_of_ne
    (entropy_outcome_ge_of_strategy three measurable_id split .of_discrete T .of_discrete hcol)
    (no_table_attains T hcol).symm

/-- **The table-outcome reading is false**: at `D` uniform on three values and
`ρ` with blocks `{0, 1}`, `{2}`, no column-injective table attains
`H(D) − H(R)`. -/
theorem literal_false : ¬ LiteralPrint := by
  intro h
  obtain ⟨-, E, _, _, _, T, -, hcol, hEq⟩ :=
    h (Fin 3) (Fin 3) Bool three id split measurable_id .of_discrete
  exact no_table_attains T hcol hEq

/-- **The repaired minimum holds in general**, at the scope of the library's
bound (any measure that is zero or a probability, finite-range `D` and `R`,
`H_D(R) = 0`):

* every `E` on `Ω` meeting §11/8's premise `H_R(E) ≥ H_R(D)` has
  `H(E) ≥ H(D) − H(R)` (`entropy_ge_sub_of_condEntropy_eq_zero`);
* there is an extension `Ω × Fin (n + 1)` carrying a copy of `(D, R)` with the
  same joint law and `H_D(R) = 0`, on which every `E'` meeting the copy's premise
  has `H(E') ≥ H(D) − H(R)`, and the second factor meets the premise with
  `H(E) = H(D) − H(R)` (`exists_entropy_eq_sub_of_condEntropy_eq_zero`). So on the
  extension `H(D) − H(R)` is the minimum over the premise class, in print's sense:
  a bound that is reached. -/
theorem repaired_holds {Ω D R E : Type} [MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSpace R] [MeasurableSpace E] [MeasurableSingletonClass D]
    [MeasurableSingletonClass R] [MeasurableSingletonClass E] [Countable D] [Countable R]
    [Countable E] (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {Dv : Ω → D} {Rv : Ω → R} (hD : Measurable Dv) (hR : Measurable Rv)
    [FiniteRange Dv] [FiniteRange Rv] (hdet : H[Rv | Dv ; μ] = 0) :
    (∀ Ev : Ω → E, Measurable Ev → ∀ [FiniteRange Ev],
        H[Dv | Rv ; μ] ≤ H[Ev | Rv ; μ] → H[Dv ; μ] - H[Rv ; μ] ≤ H[Ev ; μ]) ∧
    ∃ (n : ℕ) (ν : Measure (Fin (n + 1))), IsProbabilityMeasure ν ∧
      IdentDistrib (fun p : Ω × Fin (n + 1) => (Dv p.1, Rv p.1)) (fun ω => (Dv ω, Rv ω))
        (μ.prod ν) μ ∧
      H[Rv ∘ Prod.fst | Dv ∘ Prod.fst ; μ.prod ν] = 0 ∧
      (∀ Ev' : Ω × Fin (n + 1) → E, Measurable Ev' → ∀ [FiniteRange Ev'],
        H[Dv ∘ Prod.fst | Rv ∘ Prod.fst ; μ.prod ν] ≤ H[Ev' | Rv ∘ Prod.fst ; μ.prod ν] →
        H[Dv ; μ] - H[Rv ; μ] ≤ H[Ev' ; μ.prod ν]) ∧
      H[Dv ∘ Prod.fst | Rv ∘ Prod.fst ; μ.prod ν]
        ≤ H[(Prod.snd : Ω × Fin (n + 1) → Fin (n + 1)) | Rv ∘ Prod.fst ; μ.prod ν] ∧
      H[(Prod.snd : Ω × Fin (n + 1) → Fin (n + 1)) ; μ.prod ν] = H[Dv ; μ] - H[Rv ; μ] := by
  refine ⟨fun _ hE _ hkey => entropy_ge_sub_of_condEntropy_eq_zero μ hD hR hE hdet hkey, ?_⟩
  obtain ⟨n, ν, hν, hlaw, hdet', hkey', hE⟩ :=
    exists_entropy_eq_sub_of_condEntropy_eq_zero μ hD hR hdet
  refine ⟨n, ν, hν, hlaw, hdet', ?_, hkey', hE⟩
  intro Ev' hE' _ hkeyE'
  have hlawD : IdentDistrib (Dv ∘ Prod.fst : Ω × Fin (n + 1) → D) Dv (μ.prod ν) μ :=
    hlaw.comp measurable_fst
  have hlawR : IdentDistrib (Rv ∘ Prod.fst : Ω × Fin (n + 1) → R) Rv (μ.prod ν) μ :=
    hlaw.comp measurable_snd
  have h := entropy_ge_sub_of_condEntropy_eq_zero (μ.prod ν) (hD.comp measurable_fst)
    (hR.comp measurable_fst) hE' hdet' hkeyE'
  rwa [hlawD.entropy_congr, hlawR.entropy_congr] at h

end AshbyElevenEightMinimumLiteral
