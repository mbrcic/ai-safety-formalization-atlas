import AISafetyAtlas.InformationTheory.DataProcessing
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Cover–Thomas Theorem 2.8.1, equality clause, as printed is false; the repaired clause holds

Thomas M. Cover and Joy A. Thomas, *Elements of Information Theory*, 2nd ed. (2006),
proof of Theorem 2.8.1 (data-processing inequality), book p. 35, PDF p. 61 (audit row
S01-R06), after (2.121), `I(X; Y) ≥ I(X; Z)`, under the hypothesis `X → Y → Z`:

    We have equality if and only if I(X; Y|Z) = 0 (i.e., X → Z → Y forms a
    Markov chain).

(Transcribed from the page image in
`docs/provenance/printed-statements/cover-thomas-2006-ch2.yaml`, entry
`ct2-thm-2.8.1-equality`.) Print's setting (`source.standing`, §2.1, PDF p. 39):
discrete random variables with probability mass functions, and no finiteness of the
alphabet. The chapter's own Problem 2.1 uses an infinite alphabet. The terms are
print's:

* (2.28)–(2.29), PDF pp. 45–46: `I(X; Y) = Σ p(x, y) log p(x, y)/(p(x)p(y)) =
  D(p(x, y) ‖ p(x)p(y))`;
* (2.26), PDF p. 45: `D(p ‖ q) = Σ p(x) log p(x)/q(x)`, with `0 log 0/q = 0` and
  `p log p/0 = ∞`;
* (2.61), PDF p. 49: `I(X; Y | Z) = E_{p(x,y,z)} log p(X, Y|Z)/(p(X|Z)p(Y|Z))`;
* (2.117), PDF p. 60: `X → Y → Z` iff `p(x, y, z) = p(x) p(y|x) p(z|y)`.

**What this file defines, and why it is print's object.** Neither Mathlib nor the
atlas has a mutual information valued in `[0, ∞]`. The library's `I[X : Y]` is PFR's
real-valued one, whose infinite sums are junk (`0`), so it cannot state the clause
where it fails. Mathlib has the relative entropy `InformationTheory.klDiv`, valued in
`ℝ≥0∞`. For probability measures it is `∫ log (dμ/dν) dμ` when `μ ≪ ν` and the
log-likelihood ratio is integrable, and `∞` otherwise. On a countable alphabet that
integral is `Σ p(x) log p(x)/q(x)`. Failure of `μ ≪ ν` is print's `p log p/0 = ∞`. The
negative part of the integrand always has a finite integral (standard; not proved
here), so non-integrability means that the series diverges to `+∞`. That is the value print's (2.26) gives. So:

* `miENN X Y μ := klDiv (law of (X, Y)) (law X ⊗ law Y)` is (2.29) verbatim;
* `cmiENN X Y Z μ := Σ_z P(Z = z) · miENN X Y (μ conditioned on Z = z)` is (2.61),
  with the expectation taken first over `z`. (2.60) defines the same quantity as
  `H(X|Z) − H(X|Y, Z)`. At the witness below, both give `H(B) − 0 = log 2`, with
  no `∞ − ∞` (this is not proved here; the file proves only `cmiENN ≠ 0`);
* `X → Y → Z` is the library's `IsMarkovChain`, tied to (2.117) by
  `isMarkovChain_iff_measure_factorizes`, which carries no finiteness hypothesis.

The logarithm is natural, where print uses base 2. The values at stake, `∞` and `0`,
do not depend on the base. `LiteralPrint` takes countable alphabets with measurable
singletons and any probability space `Ω`. What makes the refutation print's is that
the witness is fully discrete: `Ω` is `X`'s countable alphabet with measurable
singletons, `X = id`, and `μ` is the measure of a pmf. Here `I(X;Y)` denotes `miENN`.

**The witness** (from the regrade's defect record for row 201). `A` takes
values in blocks: block `k` has `2^2^(k+1)` letters of mass `2^-(k+1) · 2^-2^(k+1)`
each, so `H(A) = Σ_k 2^-(k+1) (k + 1 + 2^(k+1)) log 2 = ∞`. `B` is an independent fair
bit, `X = (A, B)`, `Y = X`, `Z = A`. Then `Z` is a function of `Y`, so
`X → Y → Z` (`markov_XYZ`). Every term of (2.28) for `I(X; Z)` lies on the graph of
`fst` and equals `p(x) log 1/p(a) ≥ 0`, so the series diverges outright:
`I(X; Z) = H(A) = ∞` (`mi_XZ_eq_top`). Data processing then gives `I(X; Y) = ∞`
(`mi_XY_eq_top`, from Mathlib's `klDiv_map_le`). So equality holds. But given `A = a`,
`Y` still copies the fair bit `B`, so `I(X; Y | Z) ≠ 0` (`cmi_ne_zero`, in fact
`= log 2`) and `X → Z → Y` fails (`not_markov_XZY`). Both readings of the clause are
refuted: `not_literalPrint` and `not_literalPrintMarkov`.

Why the repair is the necessary one and not a different theorem:

* print's proof rests on the chain rule (2.119)/(2.120), transcribed in the yaml's
  note on `ct2-thm-2.5.2`:
  `I(X; Y, Z) = I(X; Z) + I(X; Y|Z) = I(X; Y) + I(X; Z|Y)`. On the atlas's reading
  of the proof, `X → Y → Z` gives `I(X; Z|Y) = 0`, hence
  `I(X; Z) + I(X; Y|Z) = I(X; Y)`. The inequality survives in `[0, ∞]` (not proved
  here). Concluding `I(X; Y|Z) = 0` from `I(X; Y) = I(X; Z)` cancels the common
  value, and that is valid exactly when it is finite. At the witness the identity
  reads `∞ + log 2 = ∞`;
* so only the "only if" direction fails, and only at `I(X; Y) = ∞`. The witness
  uses nothing else (`not_literalPrint` applies `.mp`). The "if" direction needs no
  finiteness: `I(X; Y|Z) = 0` gives `I(X; Z) = I(X; Y, Z) = I(X; Y)` by the same
  chain rule in `[0, ∞]` (not proved here). The repair graded for this row restricts
  the whole clause to `I(X; Y) < ∞`. That is coarser than necessary; the minimal
  repair restricts only "only if". Finite `I(X; Y)` is weaker than finite `H(X)`,
  which is weaker again than a finite alphabet. That the repaired clause holds on
  every countable-alphabet instance with `I(X; Y) < ∞` is the cancellation argument
  above. It needs the chain rule in `[0, ∞]` for countable alphabets, which the
  atlas does not prove;
* `repaired_holds` is what the library proves: the clause, in both readings, for
  `FiniteRange` `X`, `Y`, `Z` (`mutualInfo_eq_iff_isMarkovChain`,
  `isMarkovChain_iff_condMutualInfo_eq_zero`). There `I(X; Y) ≤ log |range X| < ∞`,
  and PFR's real `I` is the finite value of (2.28). The bridge from PFR's `I` to
  `miENN` is not proved here. `repaired_holds` covers finite alphabets only, not
  the whole repair.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/cover-thomas-2-8-1-literal.lean`. Grading
context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired slips).
-/

open MeasureTheory ProbabilityTheory InformationTheory AISafetyAtlas.InformationTheory
open scoped ENNReal

namespace CoverThomasTwoEightOneLiteral

section Definitions

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U]

/-- **Mutual information in `[0, ∞]`**, Cover–Thomas (2.28)–(2.29): the relative
entropy between the joint law of `(X, Y)` and the product of the marginals. -/
noncomputable def miENN (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ≥0∞ :=
  klDiv (μ.map fun ω => (X ω, Y ω)) ((μ.map X).prod (μ.map Y))

/-- **Conditional mutual information in `[0, ∞]`**, Cover–Thomas (2.61):
`E_{p(z)}` of the relative entropy between `p(x, y | z)` and `p(x | z) p(y | z)`. -/
noncomputable def cmiENN (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) : ℝ≥0∞ :=
  ∑' z : U, μ (Z ⁻¹' {z}) * miENN X Y (μ[|Z ⁻¹' {z}])

end Definitions

/-- The equality clause exactly as printed, in print's setting (discrete random
variables on countable alphabets, mutual information valued in `[0, ∞]`): if
`X → Y → Z`, then `I(X; Y) = I(X; Z)` if and only if `I(X; Y | Z) = 0`. -/
def LiteralPrint : Prop :=
  ∀ (Ω S T U : Type) [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSpace U] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] [Countable S] [Countable T] [Countable U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T) (Z : Ω → U),
    Measurable X → Measurable Y → Measurable Z → IsMarkovChain X Y Z μ →
      (miENN X Y μ = miENN X Z μ ↔ cmiENN X Y Z μ = 0)

/-- The parenthetical reading of the same clause: if `X → Y → Z`, then
`I(X; Y) = I(X; Z)` if and only if `X → Z → Y`. -/
def LiteralPrintMarkov : Prop :=
  ∀ (Ω S T U : Type) [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSpace U] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] [Countable S] [Countable T] [Countable U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T) (Z : Ω → U),
    Measurable X → Measurable Y → Measurable Z → IsMarkovChain X Y Z μ →
      (miENN X Y μ = miENN X Z μ ↔ IsMarkovChain X Z Y μ)

/-! ## Relative entropy on a countable alphabet -/

section Countable

variable {W β : Type*} [MeasurableSpace W] [MeasurableSingletonClass W] [Countable W]
  [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]

/-- On an atom of `ν`, the Radon–Nikodym derivative is the ratio of the masses. -/
theorem rnDeriv_singleton (μ ν : Measure W) [SigmaFinite μ] [SigmaFinite ν] (hac : μ ≪ ν)
    (x : W) (h0 : ν {x} ≠ 0) (htop : ν {x} ≠ ∞) : μ.rnDeriv ν x = μ {x} / ν {x} := by
  have h := congrArg (fun m : Measure W => m {x}) (Measure.withDensity_rnDeriv_eq μ ν hac)
  simp only [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton] at h
  rw [← h, ENNReal.mul_div_cancel_right h0 htop]

/-- **`I(X; g(X)) = ∞` once `∑ p(w) |log p_{g(X)}(g w)|` diverges.** The joint law of
`(X, g X)` sits on the graph of `g`, where the likelihood ratio against the product
law is `1 / p_{g(X)}(g w)`; so the log-likelihood ratio is not integrable. -/
theorem klDiv_graph_eq_top (μ : Measure W) [IsProbabilityMeasure μ] (g : W → β)
    (hpos : ∀ w, μ {w} ≠ 0)
    (hdiv : ∑' w, ‖Real.log ((μ.map g) {g w}).toReal‖ₑ * μ {w} = ∞) :
    klDiv (μ.map fun w => (w, g w)) (μ.prod (μ.map g)) = ∞ := by
  have hm : Measurable fun w => (w, g w) := measurable_of_countable _
  rw [klDiv_eq_top_iff]
  intro hac hint
  have hfin := hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral
  rw [lintegral_map (measurable_of_countable _) hm, lintegral_countable'] at hfin
  refine hfin.ne (Eq.trans (tsum_congr fun w => ?_) hdiv)
  congr 1
  have hgw : (μ.map g) {g w} ≠ 0 := by
    rw [Measure.map_apply (measurable_of_countable g) (measurableSet_singleton _)]
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (hpos w))
      (measure_mono fun x hx => by simp_all))
  have hJ : (μ.map fun w => (w, g w)) {(w, g w)} = μ {w} := by
    rw [Measure.map_apply hm (measurableSet_singleton _)]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ rfl⟩⟩
  have hP : (μ.prod (μ.map g)) {(w, g w)} = μ {w} * (μ.map g) {g w} := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  have hratio : μ {w} / (μ {w} * (μ.map g) {g w}) = ((μ.map g) {g w})⁻¹ := by
    rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (hpos w)) (Or.inl (measure_ne_top _ _)),
      mul_comm (μ {w})⁻¹, mul_assoc, ENNReal.inv_mul_cancel (hpos w) (measure_ne_top _ _),
      mul_one]
  rw [llr_def]
  beta_reduce
  rw [rnDeriv_singleton _ _ hac _ (by rw [hP]; exact mul_ne_zero (hpos w) hgw)
      (by rw [hP]; exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    hJ, hP, hratio, ENNReal.toReal_inv, Real.log_inv, enorm_neg]

end Countable

/-! ## The witness -/

/-- Block `k` of `A`'s alphabet has `2 ^ 2 ^ (k + 1)` letters. -/
abbrev blockSize (k : ℕ) : ℕ := 2 ^ 2 ^ (k + 1)

/-- `A`'s alphabet: the disjoint union of the blocks. -/
def Alph : Type := Σ k : ℕ, Fin (blockSize k)

/-- The block a letter lies in. -/
def Alph.blk (a : Alph) : ℕ := Sigma.fst a

instance : MeasurableSpace Alph := ⊤
instance : MeasurableSingletonClass Alph := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
instance : Countable Alph := inferInstanceAs (Countable (Σ k : ℕ, Fin (blockSize k)))

/-- Each letter of block `k` has mass `2^-(k+1) · 2^-(2^(k+1))`, i.e. `2^-ex k`. -/
def ex (k : ℕ) : ℕ := k + 1 + 2 ^ (k + 1)

/-- `X = (A, B)`'s alphabet. -/
abbrev W : Type := Alph × Bool

/-- `p(a, b) = p(a) / 2`: `B` is a fair bit independent of `A`. -/
noncomputable def mass (w : W) : ℝ≥0∞ := 2⁻¹ ^ (ex w.1.blk + 1)

theorem two_mul_half (x : ℝ≥0∞) : 2 * (x * 2⁻¹) = x := by
  rw [mul_comm x, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

theorem blockSize_mul (k : ℕ) : (blockSize k : ℝ≥0∞) * 2⁻¹ ^ 2 ^ (k + 1) = 1 := by
  rw [blockSize, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]

/-- Block `k` carries mass `2^-(k+1)`. -/
theorem block_sum (k : ℕ) :
    ∑' _ : Fin (blockSize k), (2⁻¹ : ℝ≥0∞) ^ ex k = 2⁻¹ ^ (k + 1) := by
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ex,
    pow_add, mul_left_comm, blockSize_mul, mul_one]

theorem mass_sum : ∑' w : W, mass w = 1 := by
  rw [show (∑' w : W, mass w) = ∑' (a : Alph) (_ : Bool), (2⁻¹ : ℝ≥0∞) ^ (ex a.blk + 1) from
    ENNReal.tsum_prod (f := fun (a : Alph) (_ : Bool) => (2⁻¹ : ℝ≥0∞) ^ (ex a.blk + 1))]
  simp only [tsum_fintype, Fintype.sum_bool, ← two_mul, pow_succ, two_mul_half]
  rw [show (∑' a : Alph, (2⁻¹ : ℝ≥0∞) ^ ex a.blk)
      = ∑' (k : ℕ) (_ : Fin (blockSize k)), (2⁻¹ : ℝ≥0∞) ^ ex k from
    ENNReal.tsum_sigma' (β := fun k => Fin (blockSize k)) (fun a => (2⁻¹ : ℝ≥0∞) ^ ex a.1)]
  simp only [block_sum]
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- The law of `X = (A, B)`. -/
noncomputable def pmf : PMF W := ⟨mass, ENNReal.summable.hasSum_iff.mpr mass_sum⟩

/-- The sample space is `X`'s alphabet, with `X`'s law. -/
noncomputable def μ : Measure W := pmf.toMeasure

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

theorem μ_singleton (w : W) : μ {w} = mass w :=
  PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)

theorem μ_singleton_ne_zero (w : W) : μ {w} ≠ 0 := by
  rw [μ_singleton]
  exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)

/-- The law of `A = fst X`: `p(a) = 2^-ex k` on block `k`. -/
theorem μ_fst (a : Alph) : μ (Prod.fst ⁻¹' {a}) = 2⁻¹ ^ ex a.blk := by
  have : Prod.fst ⁻¹' {a} = ({(a, false)} ∪ {(a, true)} : Set W) := by
    ext ⟨a', b⟩
    cases b <;> simp
  rw [this, measure_union (Set.disjoint_singleton.mpr (by simp)) (measurableSet_singleton _),
    μ_singleton, μ_singleton]
  simp only [mass]
  rw [← two_mul, pow_succ, two_mul_half]

theorem enorm_log_inv_two_pow (n : ℕ) :
    ‖Real.log (((2 : ℝ≥0∞)⁻¹ ^ n).toReal)‖ₑ = ENNReal.ofReal (n * Real.log 2) := by
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, Real.log_pow, Real.log_inv,
    mul_neg, enorm_neg, Real.enorm_of_nonneg (by positivity)]

/-- **`H(A) = ∞`**, in the form `klDiv_graph_eq_top` reads: block `k` contributes at
least `log 2 / 2`. -/
theorem entropy_fst_eq_top :
    ∑' w : W, ‖Real.log ((μ.map Prod.fst) {w.1}).toReal‖ₑ * μ {w} = ∞ := by
  simp only [Measure.map_apply measurable_fst (measurableSet_singleton _), μ_fst,
    enorm_log_inv_two_pow, μ_singleton, mass]
  set f : W → ℝ≥0∞ := fun w => ENNReal.ofReal (ex w.1.blk * Real.log 2) * 2⁻¹ ^ (ex w.1.blk + 1)
  have hinj : Function.Injective fun a : Alph => (a, false) := fun _ _ h => congrArg Prod.fst h
  refine top_le_iff.mp (le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj f))
  rw [show (∑' a : Alph, f (a, false))
      = ∑' (k : ℕ) (j : Fin (blockSize k)), f (⟨k, j⟩, false) from
    ENNReal.tsum_sigma' (β := fun k => Fin (blockSize k)) (fun a => f (a, false))]
  have hL : ENNReal.ofReal (Real.log 2) * 2⁻¹ ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.log_pos one_lt_two)).ne'
      (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
  rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) hL]
  refine ENNReal.tsum_le_tsum fun k => ?_
  have hcancel : (2 : ℝ≥0∞) ^ (k + 1) * 2⁻¹ ^ (k + 1) = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  have hR : (2 : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (Real.log 2)
      ≤ ENNReal.ofReal (ex k * Real.log 2) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow zero_le_two,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg one_le_two))
    exact_mod_cast (Nat.le_add_left _ _ : 2 ^ (k + 1) ≤ k + 1 + 2 ^ (k + 1))
  have hp : (2⁻¹ : ℝ≥0∞) ^ (ex k + 1) = 2⁻¹ ^ (k + 1) * 2⁻¹ ^ 2 ^ (k + 1) * 2⁻¹ := by
    rw [ex, pow_add, pow_add, pow_one]
  simp only [f, Alph.blk, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  calc ENNReal.ofReal (Real.log 2) * 2⁻¹
      = 2 ^ (k + 1) * ENNReal.ofReal (Real.log 2) * 2⁻¹ ^ (k + 1) * 2⁻¹ := by
        rw [show (2 : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (Real.log 2) * 2⁻¹ ^ (k + 1) * 2⁻¹
            = ENNReal.ofReal (Real.log 2) * 2⁻¹ * (2 ^ (k + 1) * 2⁻¹ ^ (k + 1)) by ring,
          hcancel, mul_one]
    _ ≤ ENNReal.ofReal (ex k * Real.log 2) * 2⁻¹ ^ (k + 1) * 2⁻¹ := by gcongr
    _ = ENNReal.ofReal (ex k * Real.log 2) * 2⁻¹ ^ (k + 1) * 2⁻¹
          * ((blockSize k : ℝ≥0∞) * 2⁻¹ ^ 2 ^ (k + 1)) := by rw [blockSize_mul, mul_one]
    _ = (blockSize k : ℝ≥0∞) * (ENNReal.ofReal (ex k * Real.log 2) * 2⁻¹ ^ (ex k + 1)) := by
        rw [hp]; ring

/-- **`I(X; A) = ∞`.** -/
theorem mi_XZ_eq_top : miENN id Prod.fst μ = ∞ := by
  rw [miENN, Measure.map_id]
  exact klDiv_graph_eq_top μ Prod.fst μ_singleton_ne_zero entropy_fst_eq_top

/-- **`I(X; X) = ∞`**, from `I(X; A) = ∞` by data processing along `Prod.map id fst`. -/
theorem mi_XY_eq_top : miENN id id μ = ∞ := by
  have hmap := klDiv_map_le (μ.map fun w : W => (id w, id w)) ((μ.map id).prod (μ.map id))
    (measurable_id.prodMap measurable_fst : Measurable (Prod.map (id : W → W) Prod.fst))
  rw [Measure.map_map (measurable_id.prodMap measurable_fst) (measurable_of_countable _),
    Measure.map_id, ← Measure.map_prod_map μ μ measurable_id measurable_fst, Measure.map_id] at hmap
  rw [miENN, ← top_le_iff, ← mi_XZ_eq_top, miENN, Measure.map_id]
  exact hmap

/-- `X → Y → Z` for `Y = X`, `Z = A = fst X`: `Z` is a function of `Y`. Proved from
the factorization (2.117), via the library's bridge, with no finiteness. -/
theorem markov_XYZ : IsMarkovChain (id : W → W) (id : W → W) Prod.fst μ := by
  rw [isMarkovChain_iff_measure_factorizes measurable_id]
  intro y s t _ _
  simp only [Set.preimage_id]
  by_cases hs : y ∈ s <;> by_cases ht : y ∈ Prod.fst ⁻¹' t
  · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hs),
      Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr ht)]
  · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hs),
      Set.singleton_inter_eq_empty.mpr ht]
  · rw [Set.inter_singleton_eq_empty.mpr hs, Set.empty_inter, measure_empty, mul_zero, zero_mul]
  · rw [Set.inter_singleton_eq_empty.mpr hs, Set.empty_inter, measure_empty, mul_zero, zero_mul]

/-- The first letter of block `0`. -/
def a₀ : Alph := ⟨0, ⟨0, Nat.two_pow_pos _⟩⟩

theorem fst_ne_zero : μ (Prod.fst ⁻¹' {a₀}) ≠ 0 := by
  rw [μ_fst]
  exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)

/-- **`X → Z → Y` fails**: given `A = a₀`, `X` and `Y = X` are not conditionally
independent, since `B` is still a fair bit and `Y` copies it. -/
theorem not_markov_XZY : ¬ IsMarkovChain (id : W → W) Prod.fst (id : W → W) μ := by
  rw [isMarkovChain_iff_measure_factorizes measurable_fst]
  intro h
  have := h a₀ {(a₀, false)} {(a₀, true)} (measurableSet_singleton _) (measurableSet_singleton _)
  change μ (Prod.fst ⁻¹' {a₀}) * μ ({(a₀, false)} ∩ Prod.fst ⁻¹' {a₀} ∩ {(a₀, true)})
    = μ ({(a₀, false)} ∩ Prod.fst ⁻¹' {a₀}) * μ (Prod.fst ⁻¹' {a₀} ∩ {(a₀, true)}) at this
  have e1 : ({(a₀, false)} ∩ Prod.fst ⁻¹' {a₀} ∩ {(a₀, true)} : Set W) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨rfl, -⟩, h⟩
    simp at h
  rw [e1, Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (by simp)),
    Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr (by simp)), measure_empty,
    mul_zero] at this
  exact mul_ne_zero (μ_singleton_ne_zero _) (μ_singleton_ne_zero _) this.symm

/-- **`I(X; Y | Z) ≠ 0`**: the conditional law of `(X, Y)` given `A = a₀` puts no mass on
`((a₀, false), (a₀, true))`, which the product of the conditional marginals weighs. -/
theorem cmi_ne_zero : cmiENN (id : W → W) (id : W → W) Prod.fst μ ≠ 0 := by
  intro h
  have h0 := ENNReal.tsum_eq_zero.mp h a₀
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact fst_ne_zero h1
  rw [miENN, klDiv_eq_zero_iff] at h1
  have h2 : (μ[|Prod.fst ⁻¹' {a₀}]).map (fun ω : W => (id ω, id ω)) {((a₀, false), (a₀, true))}
      = ((μ[|Prod.fst ⁻¹' {a₀}]).map id).prod ((μ[|Prod.fst ⁻¹' {a₀}]).map id)
        {((a₀, false), (a₀, true))} := by rw [h1]
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    ← Set.singleton_prod_singleton, Measure.prod_prod, Measure.map_id] at h2
  have hempty : (fun ω : W => (id ω, id ω)) ⁻¹' ({(a₀, false)} ×ˢ {(a₀, true)}) = ∅ := by
    ext ω
    simp only [id, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro h3 h4
    rw [h3] at h4
    simp at h4
  have hν : ∀ b : Bool, μ[{(a₀, b)} | Prod.fst ⁻¹' {a₀}] ≠ 0 := by
    intro b
    rw [cond_apply (measurable_fst (measurableSet_singleton a₀)) μ,
      Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr (by simp))]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (μ_singleton_ne_zero _)
  rw [hempty, measure_empty] at h2
  exact mul_ne_zero (hν false) (hν true) h2.symm

/-- **The printed equality clause is false.** At `X = (A, B)`, `Y = X`, `Z = A`, the chain
`X → Y → Z` holds and `I(X; Y) = ∞ = I(X; Z)`, yet `I(X; Y | Z) ≠ 0`. -/
theorem not_literalPrint : ¬ LiteralPrint := by
  intro h
  have := h W W W Alph μ id id Prod.fst measurable_id measurable_id measurable_fst markov_XYZ
  exact cmi_ne_zero (this.mp (by rw [mi_XY_eq_top, mi_XZ_eq_top]))

/-- **The parenthetical reading is false too**, on the same witness. -/
theorem not_literalPrintMarkov : ¬ LiteralPrintMarkov := by
  intro h
  have := h W W W Alph μ id id Prod.fst measurable_id measurable_id measurable_fst markov_XYZ
  exact not_markov_XZY (this.mp (by rw [mi_XY_eq_top, mi_XZ_eq_top]))

/-- **The repaired clause holds on finite alphabets**, as the library proves it: for
`FiniteRange` `X`, `Y`, `Z` (so `I(X; Y) < ∞`) with `X → Y → Z`, equality holds iff
`I(X; Y | Z) = 0` iff `X → Z → Y`. PFR's real-valued `I`; countable alphabets with
finite `I(X; Y)` are not covered. -/
theorem repaired_holds {Ω S T U : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSpace T] [MeasurableSpace U] [MeasurableSingletonClass S]
    [MeasurableSingletonClass T] [MeasurableSingletonClass U] [Countable S] [Countable T]
    [Countable U] (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T}
    {Z : Ω → U} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] (h : IsMarkovChain X Y Z μ) :
    (I[X : Y ; μ] = I[X : Z ; μ] ↔ I[X : Y | Z ; μ] = 0) ∧
      (I[X : Y ; μ] = I[X : Z ; μ] ↔ IsMarkovChain X Z Y μ) := by
  have h1 := mutualInfo_eq_iff_isMarkovChain μ hX hY hZ h
  have h2 := isMarkovChain_iff_condMutualInfo_eq_zero (μ := μ) (Y := Z) (Z := Y) hX hY
  exact ⟨eq_comm.trans (h1.trans h2), eq_comm.trans h1⟩

end CoverThomasTwoEightOneLiteral
