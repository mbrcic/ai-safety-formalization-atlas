import AISafetyAtlas.Learning.Sharp

/-!
Igel and Toussaint, *A No-Free-Lunch Theorem for Non-Uniform Distributions of Target
Functions* (2004), Theorem 5, p. 320. A probability on objectives is constant on each
histogram class iff the expected Kronecker indicator of any performance measure agrees
for every pair of non-repeating algorithms at lengths `1, …, |X|`.

The cited declarations are `nfl_adaptive_iff_permInvariant`,
`nfl_mixture_of_permInvariant`, and `basisClass_histogram_eq_permOrbit`.
The affine normalization pairs a shifted probability with the uniform probability.
The two printed conclusions allow cancellation of the shift. Pair-history algorithms
are compared through the cost sequences they produce. The stochastic clause follows
by taking mixtures of the deterministic behaviours.

Checked: `lake env lean docs/provenance/transfers/061-weighted-no-free-lunch.lean`
-/

namespace Transfer061

open AISafetyAtlas.Learning AISafetyAtlas.Combinatorics Function
open Classical
open scoped BigOperators

universe uX uY

variable {X : Type uX} {Y : Type uY}

noncomputable def delta {α : Type*} (k : ℝ) (c : α → ℝ) (x : α) : ℝ :=
  open Classical in if k = c x then 1 else 0

def NonRepeating {m : ℕ} (r : AdaptiveRule X Y m) : Prop :=
  ∀ c, Injective (ruleVisit r c)

private theorem replay_values (a : List (X × Y) → X) (n : ℕ) (c : Fin n → Y) :
    (replay a n c).map Prod.snd = List.ofFn c := by
  induction n with
  | zero => simp [replay]
  | succ n ih =>
    rw [replay, List.map_append, ih, List.ofFn_succ_last]
    rfl

private theorem trace_values (a : List (X × Y) → X) (f : X → Y) (m : ℕ) :
    (traceRun a f m).map Prod.snd = List.ofFn (observed (searchRule m a) f) :=
  replay_observed a f ▸ replay_values a m (observed (searchRule m a) f)

/-- Print's cost sequence reads the second coordinate of each explored pair. -/
def printCosts (m : ℕ) (a : List (X × Y) → X) (f : X → Y) (i : Fin m) : Y :=
  ((traceRun a f m).map Prod.snd)[i.val]'(by simp [trace_values])

private theorem printCosts_eq (m : ℕ) (a : List (X × Y) → X) (f : X → Y) :
    printCosts m a f = observed (searchRule m a) f := by
  funext i
  simp [printCosts, trace_values]

section Finite

variable [Fintype X] [Fintype Y]

def IsProbability (p : ObjectiveWeight X Y) : Prop :=
  (∀ f, 0 ≤ p f) ∧ ∑ f, p f = 1

def HistogramInvariant [DecidableEq Y] (p : ObjectiveWeight X Y) : Prop :=
  ∀ f g : X → Y, histogram f = histogram g → p f = p g

def PrintNFL (p : ObjectiveWeight X Y) : Prop :=
  ∀ (m : ℕ), 0 < m → m ≤ Fintype.card X → ∀ (c : (Fin m → Y) → ℝ) (k : ℝ)
    (a b : List (X × Y) → X), NonRepeating (searchRule m a) →
    NonRepeating (searchRule m b) →
    (∑ f, p f * delta k c (printCosts m a f)) = ∑ f, p f * delta k c (printCosts m b f)

def LeanNFL (P : ObjectiveWeight X Y) : Prop :=
  ∀ (m : ℕ) (Ψ : (Fin m → Y) → ℝ) (r₁ r₂ : AdaptiveRule X Y m),
    NonRepeating r₁ → NonRepeating r₂ → weightedTrace P Ψ r₁ = weightedTrace P Ψ r₂

def PrintStatement : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [Fintype X] [Fintype Y] [DecidableEq Y]
    (p : ObjectiveWeight X Y), IsProbability p → (HistogramInvariant p ↔ PrintNFL p)

def LeanStatement : Prop :=
  (∀ (X : Type uX) (Y : Type uY) [Fintype X] [Fintype Y] (P : ObjectiveWeight X Y),
    LeanNFL P ↔ PermInvariant P) ∧
  (∀ (X : Type uX) (Y : Type uY) [Fintype X] [Fintype Y] [DecidableEq Y]
    {m : ℕ} {P : ObjectiveWeight X Y}, PermInvariant P → ∀ (p q : AdaptiveRule X Y m → ℝ),
    (∑ a, p a) = (∑ a, q a) →
    (∀ a, p a ≠ 0 → NonRepeating a) → (∀ a, q a ≠ 0 → NonRepeating a) →
    ∀ Ψ, mixtureTrace P Ψ p = mixtureTrace P Ψ q)

omit [Fintype Y] in
private theorem histogram_iff [DecidableEq X] [DecidableEq Y] (p : ObjectiveWeight X Y) :
    HistogramInvariant p ↔ PermInvariant p := by
  constructor
  · intro h π f
    have hmem : f ∘ π ∈ basisClass (histogram f) :=
      (basisClass_histogram_eq_permOrbit f).symm ▸ (show f ∘ π ∈ permOrbit f from ⟨π, rfl⟩)
    exact h (f ∘ π) f hmem
  · intro h f g hfg
    have hmem : f ∈ basisClass (histogram g) := hfg
    obtain ⟨π, rfl⟩ := (basisClass_histogram_eq_permOrbit g) ▸ hmem
    exact h π g

private def replayRule {m : ℕ} (x : X) (r : AdaptiveRule X Y m) (t : List (Y)) : X :=
  if hk : t.length < m then r ⟨t.length, hk⟩ t.get else x

omit [Fintype X] [Fintype Y] in
private theorem searchRule_replayRule {m : ℕ} (x : X) (r : AdaptiveRule X Y m) :
    searchRule m (fun t ↦ replayRule x r (t.map Prod.snd)) = r := by
  funext k c
  rw [searchRule, replay_values]
  have recover (l : List Y) (hlen : l.length = k.val)
      (hv : ∀ i : Fin k.val, l[i.val]'(by omega) = c i) : replayRule x r l = r k c := by
    obtain ⟨k, hk⟩ := k
    dsimp at hlen hv
    subst k
    rw [replayRule, dif_pos hk]
    congr 1
    exact funext hv
  apply recover _ List.length_ofFn
  intro i
  simp

private noncomputable def indicator {α : Type*} (d : α) (t : α) : ℝ :=
  open Classical in if t = d then 1 else 0

private theorem expand_trace (P : ObjectiveWeight X Y) {m : ℕ}
    (Ψ : (Fin m → Y) → ℝ) (r : AdaptiveRule X Y m) :
    weightedTrace P Ψ r =
      ∑ d : Fin m → Y, Ψ d * weightedTrace P (indicator d) r := by
  classical
  simp only [weightedTrace, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp [indicator, mul_ite, eq_comm, mul_comm]

private theorem printNFL_iff_of_nonempty [Nonempty (X → Y)] (P : ObjectiveWeight X Y) :
    PrintNFL P ↔ LeanNFL P := by
  classical
  refine ⟨?_, fun h m _ _ c k a b ha hb ↦ ?_⟩
  · intro h m Ψ r₁ r₂ hr₁ hr₂
    by_cases hm : 0 < m
    · let x := r₁ ⟨0, hm⟩ (fun i ↦ i.elim0)
      let a (t : List (X × Y)) := replayRule x r₁ (t.map Prod.snd)
      let b (t : List (X × Y)) := replayRule x r₂ (t.map Prod.snd)
      have ha : searchRule m a = r₁ := searchRule_replayRule x r₁
      have hb : searchRule m b = r₂ := searchRule_replayRule x r₂
      have hcard : m ≤ Fintype.card X := by
        simpa using Fintype.card_le_of_injective _
          (hr₁ (observed r₁ (Classical.choice ‹Nonempty (X → Y)›)))
      rw [expand_trace P Ψ r₁, expand_trace P Ψ r₂]
      refine Finset.sum_congr rfl fun d _ ↦ congrArg (Ψ d * ·) ?_
      have hdelta : delta 1 (indicator d) = indicator d := by
        funext t
        by_cases he : t = d <;> simp [delta, indicator, he]
      simpa only [weightedTrace, printCosts_eq, hdelta, ha, hb] using
        h m hm hcard (indicator d) 1 a b (ha.symm ▸ hr₁) (hb.symm ▸ hr₂)
    · obtain rfl : m = 0 := by omega
      have he : r₁ = r₂ := funext fun k ↦ k.elim0
      rw [he]
  · simpa only [printCosts_eq, weightedTrace] using h m (delta k c) _ _ ha hb

private noncomputable def shift (P : ObjectiveWeight X Y) : ℝ := 1 + ∑ f, |P f|

private noncomputable def mass (P : ObjectiveWeight X Y) : ℝ := ∑ f, (P f + shift P)

private noncomputable def normalize (P : ObjectiveWeight X Y) : ObjectiveWeight X Y :=
  fun f ↦ (P f + shift P) / mass P

noncomputable def phi (P : ObjectiveWeight X Y) :
    ObjectiveWeight X Y × ObjectiveWeight X Y :=
  (normalize P, normalize 0)

private theorem shifted_pos (P : ObjectiveWeight X Y) (f : X → Y) : 0 < P f + shift P := by
  have h : |P f| ≤ ∑ g, |P g| :=
    Finset.single_le_sum (f := fun g ↦ |P g|) (fun g _ ↦ abs_nonneg (P g)) (Finset.mem_univ f)
  rw [shift, add_left_comm]
  exact add_pos_of_pos_of_nonneg zero_lt_one <|
    neg_le_iff_add_nonneg.mp ((neg_le_neg h).trans (neg_abs_le _))

private theorem mass_pos [Nonempty (X → Y)] (P : ObjectiveWeight X Y) : 0 < mass P :=
  Finset.sum_pos (fun f _ ↦ shifted_pos P f) Finset.univ_nonempty

private theorem normalized_probability [Nonempty (X → Y)] (P : ObjectiveWeight X Y) :
    IsProbability (normalize P) := by
  refine ⟨fun f ↦ (div_pos (shifted_pos P f) (mass_pos P)).le, ?_⟩
  simp only [normalize, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (mass_pos P).ne'

theorem print_hyp [Nonempty (X → Y)] (P : ObjectiveWeight X Y) :
    IsProbability (phi P).1 ∧ IsProbability (phi P).2 :=
  ⟨normalized_probability P, normalized_probability 0⟩

private theorem normalize_perm_iff [Nonempty (X → Y)] (P : ObjectiveWeight X Y) :
    PermInvariant (normalize P) ↔ PermInvariant P := by
  constructor
  · intro h π f
    exact add_right_cancel ((div_left_inj' (mass_pos P).ne').mp (h π f))
  · intro h π f
    simp only [normalize, h π f]

private theorem affine_trace (P : ObjectiveWeight X Y) {m : ℕ} (Ψ : (Fin m → Y) → ℝ)
    (r : AdaptiveRule X Y m) :
    weightedTrace (normalize P) Ψ r =
      (weightedTrace P Ψ r + shift P * weightedTrace (fun _ ↦ 1) Ψ r) / mass P := by
  simp only [weightedTrace, normalize, div_eq_mul_inv, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f _
  rw [mul_right_comm, add_mul, one_mul]

private theorem uniform_trace [Nonempty (X → Y)] (h : LeanNFL (normalize (0 : ObjectiveWeight X Y))) :
    LeanNFL (fun _ : X → Y ↦ 1) := by
  intro m Ψ a b ha hb
  have he := h m Ψ a b ha hb
  have hshift : shift (0 : ObjectiveWeight X Y) = 1 := by simp [shift]
  rw [affine_trace, affine_trace, hshift] at he
  have hz (r : AdaptiveRule X Y m) : weightedTrace 0 Ψ r = 0 := by simp [weightedTrace]
  simp only [hz, zero_add, one_mul] at he
  exact (div_left_inj' (mass_pos (0 : ObjectiveWeight X Y)).ne').mp he

private theorem affine_nfl_iff [Nonempty (X → Y)] (P : ObjectiveWeight X Y)
    (hu : LeanNFL (normalize (0 : ObjectiveWeight X Y))) :
    LeanNFL (normalize P) ↔ LeanNFL P := by
  have huni := uniform_trace hu
  constructor
  · intro h m Ψ a b ha hb
    have he := h m Ψ a b ha hb
    rw [affine_trace, affine_trace, huni m Ψ a b ha hb] at he
    exact add_right_cancel ((div_left_inj' (mass_pos P).ne').mp he)
  · intro h m Ψ a b ha hb
    rw [affine_trace, affine_trace, h m Ψ a b ha hb, huni m Ψ a b ha hb]

theorem lean_concl [DecidableEq Y] [Nonempty (X → Y)] (P : ObjectiveWeight X Y)
    (hq : HistogramInvariant (phi P).1 ↔ PrintNFL (phi P).1)
    (hu : HistogramInvariant (phi P).2 ↔ PrintNFL (phi P).2) :
    LeanNFL P ↔ PermInvariant P := by
  classical
  have hu' : LeanNFL (normalize (0 : ObjectiveWeight X Y)) :=
    (printNFL_iff_of_nonempty _).mp (hu.mp fun _ _ _ ↦ rfl)
  exact (affine_nfl_iff P hu').symm.trans ((printNFL_iff_of_nonempty _).symm.trans
    (hq.symm.trans ((histogram_iff _).trans (normalize_perm_iff P))))

private theorem nfl_empty [IsEmpty (X → Y)] (P : ObjectiveWeight X Y) :
    LeanNFL P ↔ PermInvariant P :=
  ⟨fun _ _ f ↦ isEmptyElim f, fun _ _ _ _ _ _ _ ↦ by simp [weightedTrace]⟩

private theorem mixture_of_nfl [DecidableEq Y] {m : ℕ} {P : ObjectiveWeight X Y}
    (h : LeanNFL P) (p q : AdaptiveRule X Y m → ℝ) (hmass : (∑ a, p a) = ∑ a, q a)
    (hp : ∀ a, p a ≠ 0 → NonRepeating a) (hq : ∀ a, q a ≠ 0 → NonRepeating a)
    (Ψ : (Fin m → Y) → ℝ) : mixtureTrace P Ψ p = mixtureTrace P Ψ q := by
  classical
  by_cases hex : ∃ a, NonRepeating (X := X) (Y := Y) (m := m) a
  · obtain ⟨a₀, ha₀⟩ := hex
    have factor (w : AdaptiveRule X Y m → ℝ) (hw : ∀ a, w a ≠ 0 → NonRepeating a) :
        mixtureTrace P Ψ w = (∑ a, w a) * weightedTrace P Ψ a₀ := by
      rw [mixtureTrace, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      by_cases hz : w a = 0
      · simp [hz]
      · rw [h m Ψ a a₀ (hw a hz) ha₀]
    rw [factor p hp, factor q hq, hmass]
  · have hz (w : AdaptiveRule X Y m → ℝ) (hw : ∀ a, w a ≠ 0 → NonRepeating a) (a) :
        w a = 0 := not_not.mp fun hn ↦ hex ⟨a, hw a hn⟩
    simp [mixtureTrace, hz p hp, hz q hq]

theorem lean_of_print : PrintStatement.{uX,uY} → LeanStatement.{uX,uY} := by
  intro h
  have hnfl (X : Type uX) (Y : Type uY) [Fintype X] [Fintype Y] (P : ObjectiveWeight X Y) :
      LeanNFL P ↔ PermInvariant P := by
    classical
    cases isEmpty_or_nonempty (X → Y) with
    | inl he => exact nfl_empty P
    | inr he =>
      exact lean_concl P (h X Y (phi P).1 (print_hyp P).1) (h X Y (phi P).2 (print_hyp P).2)
  exact ⟨hnfl, fun X Y _ _ _ _ P hP ↦ mixture_of_nfl ((hnfl X Y P).mpr hP)⟩

theorem print_of_lean : LeanStatement.{uX,uY} → PrintStatement.{uX,uY} := by
  intro h X Y _ _ _ p hp
  classical
  have : Nonempty (X → Y) := by
    cases isEmpty_or_nonempty (X → Y) with
    | inl he => have := hp.2; simp at this
    | inr hn => exact hn
  exact (histogram_iff p).trans ((h.1 X Y p).symm.trans (printNFL_iff_of_nonempty p).symm)

end Finite

end Transfer061
