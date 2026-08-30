module

public import AISafetyAtlas.Causal.GoalDynamics

/-!
# Persistent corruption of first-action data

The query side of MAIS-A2's goal-based setting: what an analyst sees, what an
adversary is allowed to change before it looks, and what counts as success.

## What print asks

`prob:corruption` fixes an instance `(𝐒, 𝐀, n, δ)` with `|𝐀| ≥ 2`, `n > 1` and
`(n−1)(1−δ) > 4`. All the information available to any analyst is the
**first-action map** `f_π : 𝐒 × 𝚿_n → 𝐀`. An **`η`-corruption** of an agent
`π ∈ A(E,n,δ)` is any `ρ : 𝐒 × 𝚿_n → 𝐀` differing from `f_π` on at most
`η·|𝐒 × 𝚿_n|` arguments, *"chosen by an adversary who knows the analyst's
randomized strategy but commits to `ρ` before the interaction"*. Print then calls
`η` **uniformly tolerable** when one randomized algorithm and one polynomial
budget achieve `d_∞(P̂, P) ≤ 2/√((n−1)(1−δ))` with probability at least `2/3`,
for every instance, every communicating `E`, every `π ∈ A(E,n,δ)` and every
`η`-corruption.

## Where this is print, and where it is a reading

The analyst is print's: an adaptive randomized query protocol that inspects
`f_π` at pairs of `𝐒 × 𝚿_n`, under a budget. `Conjectures.MAIS.O33` carries the
two quantifiers this module leaves to it — *one* algorithm across all instances
and *one* polynomial bounding the budget — so `TolerantAt` is print's clause
with the budget already supplied.

Two readings, both recorded rather than assumed.

1. **`ρ` is total.** Print's corruption is a map on `𝐒 × 𝚿_n`;
   `FirstActionData` is defined on every composite goal. Nothing sees the
   difference: queries are elements of `corruptionDomain n = 𝐒 × 𝚿_n`, so two
   oracles agreeing there drive the same protocol, and the budget in
   `IsCorruption` is charged against exactly those arguments.
2. **`max` is `⨆`.** Print writes `max_{π'}`, which presupposes attainment; see
   the note in `Causal.GoalDynamics`. Since `⨆ ≥ max`, `IsDeltaBoundedFull`
   selects a sub-collection of print's `A(E,n,δ)`, so a refutation quantified
   over it is the weaker claim to refute and the stronger claim once refuted.

The **adversary** is print's: `ρ` is quantified after the strategy is fixed, so
it may be chosen knowing the analyst, and it is a function fixed before the
interaction — which is what *persistent* means. The witness in
`Examples/Causal/O33Corruption.lean` uses less than that: it commits to one `ρ`
built without reading the analyst at all.

## What is not modelled

The independent-noise cousin print sets aside — *"each answer independently
randomized with probability `η`"* — would be a different type, a kernel from
queries to actions, and is not declared anywhere in this tree. Neither is print's
closing variant that *"measures the corruption budget against the set of
sequential goals only"*.
-/

namespace AISafetyAtlas.Causal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [Fintype A] [DecidableEq A]

/-! ## The oracle and the estimate -/

/-- Print's first-action data `f_π : 𝐒 × 𝚿_n → 𝐀`, carried as a total map on
composite goals. See the module note: the extra arguments are more data than
print gives the analyst, never less. -/
public abbrev FirstActionData (S A : Type*) := S → CompositeGoal S A → A

/-- What the analyst returns: an estimate `P̂_{ss'}(a)` of the transition law. -/
public abbrev KernelEstimate (S A : Type*) := S → A → S → ℝ

/-- `𝐒 × 𝚿_n`: the arguments print counts a corruption against. -/
@[expose] public def corruptionDomain (n : ℕ) : Finset (S × CompositeGoal S A) :=
  (Finset.univ : Finset S) ×ˢ compositeGoals n

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
public theorem card_corruptionDomain (n : ℕ) :
    (corruptionDomain (S := S) (A := A) n).card
      = Fintype.card S * (compositeGoals (S := S) (A := A) n).card := by
  rw [corruptionDomain, Finset.card_product, Finset.card_univ]

/-- **An `η`-corruption**: a map differing from the agent's own first actions on
at most `η·|𝐒 × 𝚿_n|` of the arguments print counts. -/
@[expose] public def IsCorruption (n : ℕ) (η : ℝ) (f ρ : FirstActionData S A) : Prop :=
  ((((corruptionDomain (S := S) (A := A) n).filter
      fun p ↦ ρ p.1 p.2 ≠ f p.1 p.2).card : ℕ) : ℝ)
    ≤ η * (((corruptionDomain (S := S) (A := A) n).card : ℕ) : ℝ)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- **The pairs a corruption has to pay for.** Fix an action `a`. The pairs
`(s, Ψ)` of `𝐒 × 𝚿_n` at which `Ψ` carries no immediate win for `(s, a)` number
`|𝐒| · (2^{Q−R} − 1)`, with `Q` the sequential goals of depth at most `n` and
`R = 2^{|𝐒||𝐀|−1}` the immediate wins. This is `Goal.card_compositeGoals_avoiding`
summed over the start states. -/
public theorem card_corruptionDomain_avoiding {n : ℕ} (hn : 1 ≤ n) (a : A) :
    ((corruptionDomain (S := S) (A := A) n).filter
        fun p ↦ Disjoint p.2 (immediateWins p.1 a)).card
      = Fintype.card S *
        (2 ^ ((boundedGoals (S := S) (A := A) n).card
          - 2 ^ (Fintype.card S * Fintype.card A - 1)) - 1) := by
  classical
  have hbi : ((corruptionDomain (S := S) (A := A) n).filter
        fun p ↦ Disjoint p.2 (immediateWins p.1 a))
      = (Finset.univ : Finset S).biUnion fun s ↦ ({s} : Finset S) ×ˢ
          ((compositeGoals n).filter fun Ψ ↦ Disjoint Ψ (immediateWins s a)) := by
    ext p
    simp only [Finset.mem_filter, corruptionDomain, Finset.mem_product, Finset.mem_univ,
      true_and, Finset.mem_biUnion, Finset.mem_singleton]
    constructor
    · rintro ⟨hΨ, hd⟩
      exact ⟨p.1, rfl, hΨ, hd⟩
    · rintro ⟨s, hs, hΨ, hd⟩
      exact ⟨hΨ, hs ▸ hd⟩
  have hdisj : ∀ s ∈ (Finset.univ : Finset S), ∀ t ∈ (Finset.univ : Finset S), s ≠ t →
      Disjoint (({s} : Finset S) ×ˢ
          ((compositeGoals n).filter fun Ψ ↦ Disjoint Ψ (immediateWins s a)))
        (({t} : Finset S) ×ˢ
          ((compositeGoals n).filter fun Ψ ↦ Disjoint Ψ (immediateWins t a))) := by
    intro s _ t _ hst
    refine Finset.disjoint_left.mpr fun p hps hpt ↦ hst ?_
    rw [Finset.mem_product, Finset.mem_singleton] at hps hpt
    rw [← hps.1, ← hpt.1]
  rw [hbi, Finset.card_biUnion hdisj]
  have hterm : ∀ s ∈ (Finset.univ : Finset S),
      (({s} : Finset S) ×ˢ
        ((compositeGoals n).filter fun Ψ ↦ Disjoint Ψ (immediateWins s a))).card
      = 2 ^ ((boundedGoals (S := S) (A := A) n).card
          - 2 ^ (Fintype.card S * Fintype.card A - 1)) - 1 := by
    intro s _
    rw [Finset.card_product, Finset.card_singleton, one_mul,
      card_compositeGoals_avoiding hn s a, card_immediateWins s a]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- **The corruption budget, discharged by the counting lemma.** A map that
agrees with the agent's first actions wherever the goal carries an immediate win
is an `η`-corruption for every `η` at least `2^{1−R}`, `R = 2^{|𝐒||𝐀|−1}`. The
bound is doubly exponentially small in `|𝐒|`, which is why one construction
serves every positive `η` at once. -/
public theorem isCorruption_of_agree_off_avoiding {n : ℕ} {η : ℝ} (hn : 1 ≤ n) (a : A)
    (f ρ : FirstActionData S A)
    (hagree : ∀ (s : S) (Ψ : CompositeGoal S A), Ψ ∈ compositeGoals n →
      ¬ Disjoint Ψ (immediateWins s a) → ρ s Ψ = f s Ψ)
    (hη : 2 / 2 ^ (2 ^ (Fintype.card S * Fintype.card A - 1)) ≤ η) :
    IsCorruption n η f ρ := by
  classical
  by_cases hS : IsEmpty S
  · have hdom : corruptionDomain (S := S) (A := A) n = ∅ := by
      rw [corruptionDomain, Finset.univ_eq_empty, Finset.empty_product]
    rw [IsCorruption, hdom]
    simp
  rw [not_isEmpty_iff] at hS
  set R := 2 ^ (Fintype.card S * Fintype.card A - 1) with hRdef
  set Q := (boundedGoals (S := S) (A := A) n).card with hQdef
  have hR1 : 1 ≤ R := Nat.one_le_two_pow
  have hRQ : R ≤ Q := by
    rw [hRdef, hQdef, ← card_immediateWins (S := S) (A := A) (Classical.arbitrary S) a]
    exact Finset.card_le_card (immediateWins_subset_boundedGoals hn _ a)
  have hsub : ((corruptionDomain (S := S) (A := A) n).filter
      fun p ↦ ρ p.1 p.2 ≠ f p.1 p.2)
      ⊆ (corruptionDomain (S := S) (A := A) n).filter
        fun p ↦ Disjoint p.2 (immediateWins p.1 a) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, ?_⟩
    by_contra hd
    exact hp.2 (hagree p.1 p.2 (by
      have := hp.1
      rw [corruptionDomain, Finset.mem_product] at this
      exact this.2) hd)
  have hcard : (((corruptionDomain (S := S) (A := A) n).filter
      fun p ↦ ρ p.1 p.2 ≠ f p.1 p.2).card : ℝ)
      ≤ ((Fintype.card S * (2 ^ (Q - R) - 1) : ℕ) : ℝ) := by
    have := Finset.card_le_card hsub
    rw [card_corruptionDomain_avoiding hn a] at this
    exact_mod_cast this
  have hYpos : (0 : ℝ) < ((2 ^ Q - 1 : ℕ) : ℝ) := by
    have : 2 ≤ 2 ^ Q := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ Q := Nat.pow_le_pow_right (by norm_num) (le_trans hR1 hRQ)
    have : 1 ≤ 2 ^ Q - 1 := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hratio : ((2 ^ (Q - R) - 1 : ℕ) : ℝ) ≤ η * ((2 ^ Q - 1 : ℕ) : ℝ) := by
    have hlt := exceptional_ratio_lt hR1 hRQ
    have hlt' : ((2 ^ (Q - R) - 1 : ℕ) : ℝ) / ((2 ^ Q - 1 : ℕ) : ℝ) ≤ η :=
      le_trans hlt.le hη
    rw [div_le_iff₀ hYpos] at hlt'
    linarith
  rw [IsCorruption, card_corruptionDomain, card_compositeGoals]
  refine le_trans hcard ?_
  push_cast
  have hSnn : (0 : ℝ) ≤ (Fintype.card S : ℝ) := Nat.cast_nonneg _
  calc (Fintype.card S : ℝ) * ((2 ^ (Q - R) - 1 : ℕ) : ℝ)
      ≤ (Fintype.card S : ℝ) * (η * ((2 ^ Q - 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hratio hSnn
    _ = η * ((Fintype.card S : ℝ) * ((2 ^ Q - 1 : ℕ) : ℝ)) := by ring

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- The uncorrupted map is an `η`-corruption of itself at every `η ≥ 0`, which
is what makes the honest world an admissible one for the adversary. -/
public theorem isCorruption_self {n : ℕ} {η : ℝ} (hη : 0 ≤ η) (f : FirstActionData S A) :
    IsCorruption n η f f := by
  classical
  have hzero : ((corruptionDomain (S := S) (A := A) n).filter
      fun p ↦ f p.1 p.2 ≠ f p.1 p.2) = ∅ := by
    refine Finset.filter_false_of_mem fun p _ ↦ ?_
    simp
  rw [IsCorruption, hzero]
  simpa using mul_nonneg hη (Nat.cast_nonneg _)

/-! ## Success -/

/-- The event print asks for with probability at least `2/3`: the estimate is
within the target radius of the true kernel, entrywise. -/
@[expose] public def reconstructionEvent (E : ControlledMarkovProcess S A) (τ : ℝ) :
    Set (KernelEstimate S A) :=
  {Q | E.WithinBall Q τ}

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq A] in
public theorem measurableSet_reconstructionEvent (E : ControlledMarkovProcess S A) (τ : ℝ) :
    MeasurableSet (reconstructionEvent E τ) := by
  have hrw : reconstructionEvent E τ
      = ⋂ s : S, ⋂ a : A, ⋂ s' : S,
        {Q : KernelEstimate S A | |Q s a s' - E.prob s a s'| ≤ τ} := by
    ext Q
    simp [reconstructionEvent, ControlledMarkovProcess.WithinBall, Set.mem_iInter]
  rw [hrw]
  refine MeasurableSet.iInter fun s ↦ MeasurableSet.iInter fun a ↦
    MeasurableSet.iInter fun s' ↦ ?_
  have hm : Measurable fun Q : KernelEstimate S A ↦ |Q s a s' - E.prob s a s'| := by
    fun_prop
  exact hm measurableSet_Iic

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A]
  [DecidableEq A] in
/-- **Two environments too far apart to share an estimate.** -/
public theorem disjoint_reconstructionEvent {E F : ControlledMarkovProcess S A} {d τ : ℝ}
    (hsep : E.SeparatedBy F d) (hd : 2 * τ < d) :
    Disjoint (reconstructionEvent E τ) (reconstructionEvent F τ) :=
  Set.disjoint_left.mpr fun _ hE hF ↦ (ControlledMarkovProcess.not_withinBall_both
    hsep hd hE hF).elim

/-! ## Print's analyst

*"All the information available to any analyst is first-action data"*, and the
budget is *"at most `p(|𝐒|,|𝐀|,n)` queries"*. So the analyst is an adaptive
randomized query protocol: it draws a pair from `𝐒 × 𝚿_n`, is told the (possibly
corrupted) first action there, and after its budget is spent returns a
distribution over estimates.

Recording the queries as well as the answers is print's information set, not
bookkeeping: two different pairs can return the same action, and a strategy
reading answers alone would have *less* than print gives it. `Causal.Query`
makes the same choice for the interventional analyst, for the same reason.

A step may be a **pass** (`none`), which is what makes the budget print's *"at
most"* rather than *"exactly"*, and keeps the strategy type inhabited when
`𝐒 × 𝚿_n` is empty. -/

/-- What the analyst may ask about: a pair of `𝐒 × 𝚿_n`. -/
public abbrev O33Query (S A : Type*) [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (n : ℕ) := ↥(corruptionDomain (S := S) (A := A) n)

/-- The analyst's record of the interaction: the pairs it asked about and the
actions it was told. -/
public abbrev FirstActionTranscript (S A : Type*) [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (n : ℕ) := List (O33Query S A n × A)

/-- A randomized adaptive query strategy: a distribution over the next query,
or over passing, given the transcript so far. -/
public abbrev FirstActionStrategy (S A : Type*) [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (n : ℕ) := FirstActionTranscript S A n → PMF (Option (O33Query S A n))

/-- The analyst's output: a distribution over estimates, read off the full
transcript. -/
public abbrev FirstActionEstimator (S A : Type*) [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [Fintype A] [DecidableEq A] (n : ℕ) :=
  FirstActionTranscript S A n → PMF (KernelEstimate S A)

/-- The law of the transcript after `N` steps. Only the analyst randomizes: the
adversary committed to `ρ` before the interaction, so each answer is determined
once the query is drawn. That is exactly what *persistent* corruption means. -/
@[expose] public noncomputable def runFirstActionTranscript (ρ : FirstActionData S A) {n : ℕ}
    (σ : FirstActionStrategy S A n) : ℕ → PMF (FirstActionTranscript S A n)
  | 0 => PMF.pure []
  | N + 1 => (runFirstActionTranscript ρ σ N).bind fun h ↦
      (σ h).map fun oq ↦ match oq with
        | none => h
        | some q => h ++ [(q, ρ q.1.1 q.1.2)]

/-- The law of the estimate the analyst returns after `N` steps. -/
@[expose] public noncomputable def outputLaw (ρ : FirstActionData S A) {n : ℕ}
    (σ : FirstActionStrategy S A n) (est : FirstActionEstimator S A n) (N : ℕ) :
    PMF (KernelEstimate S A) :=
  (runFirstActionTranscript ρ σ N).bind est

/-- Print's success clause: the estimate lands in the reconstruction ball with
probability at least `2/3`. -/
@[expose] public def Succeeds (E : ControlledMarkovProcess S A) {n : ℕ} (δ : ℝ)
    (σ : FirstActionStrategy S A n) (est : FirstActionEstimator S A n) (N : ℕ)
    (ρ : FirstActionData S A) : Prop :=
  (2 / 3 : ℝ≥0∞)
    ≤ (outputLaw ρ σ est N).toMeasure (reconstructionEvent E (reconstructionRadius n δ))

/-- **Print's uniform tolerability at one instance**, with the budget supplied
rather than derived from a polynomial. `Conjectures.MAIS.UniformlyTolerable`
carries print's single algorithm and single polynomial across all instances, and
implies this at every admissible one. -/
@[expose] public def TolerantAt (S A : Type*) [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] (n : ℕ) (δ η : ℝ) : Prop :=
  ∃ (σ : FirstActionStrategy S A n) (est : FirstActionEstimator S A n) (N : ℕ),
    ∀ E : ControlledMarkovProcess S A, E.Communicating →
      ∀ π : FullAgent S A, IsDeltaBoundedFull E π n δ →
        ∀ ρ : FirstActionData S A, IsCorruption n η (firstActionMapFull π) ρ →
          Succeeds E δ σ est N ρ

/-- **The whole of the impossibility, once a witness is supplied.** If two
communicating environments further apart than twice the target radius carry
`(δ,n)`-bounded agents whose first-action maps admit one common `η`-corruption,
then no analyst tolerates `η` at that instance: the oracle it faces is the same
function in both worlds, so its one output law would have to put `2/3` on each of
two disjoint events. No query bound is used, and the argument holds at every
budget — which is why `prob:corruption`'s polynomial plays no role here. -/
public theorem not_tolerantAt_of_common_corruption {n : ℕ} {δ η d : ℝ}
    {E₀ E₁ : ControlledMarkovProcess S A}
    (hsep : E₀.SeparatedBy E₁ d) (hd : 2 * reconstructionRadius n δ < d)
    (hcom₀ : E₀.Communicating) (hcom₁ : E₁.Communicating)
    {π₀ π₁ : FullAgent S A}
    (hb₀ : IsDeltaBoundedFull E₀ π₀ n δ) (hb₁ : IsDeltaBoundedFull E₁ π₁ n δ)
    {ρ : FirstActionData S A}
    (hr₀ : IsCorruption n η (firstActionMapFull π₀) ρ)
    (hr₁ : IsCorruption n η (firstActionMapFull π₁) ρ) :
    ¬ TolerantAt S A n δ η := by
  rintro ⟨σ, est, N, hsucc⟩
  have h₀ := hsucc E₀ hcom₀ π₀ hb₀ ρ hr₀
  have h₁ := hsucc E₁ hcom₁ π₁ hb₁ ρ hr₁
  set μ := (outputLaw ρ σ est N).toMeasure with hμ
  have hdisj := disjoint_reconstructionEvent hsep hd
  have hunion : μ (reconstructionEvent E₀ (reconstructionRadius n δ))
      + μ (reconstructionEvent E₁ (reconstructionRadius n δ))
      = μ (reconstructionEvent E₀ (reconstructionRadius n δ)
          ∪ reconstructionEvent E₁ (reconstructionRadius n δ)) :=
    (measure_union hdisj (measurableSet_reconstructionEvent E₁ _)).symm
  have hle : (2 / 3 : ℝ≥0∞) + 2 / 3 ≤ 1 := by
    calc (2 / 3 : ℝ≥0∞) + 2 / 3
        ≤ μ (reconstructionEvent E₀ (reconstructionRadius n δ))
            + μ (reconstructionEvent E₁ (reconstructionRadius n δ)) := add_le_add h₀ h₁
      _ = μ (reconstructionEvent E₀ (reconstructionRadius n δ)
            ∪ reconstructionEvent E₁ (reconstructionRadius n δ)) := hunion
      _ ≤ 1 := prob_le_one
  rw [ENNReal.div_add_div_same, ENNReal.div_le_iff (by norm_num) (by norm_num)] at hle
  norm_num at hle

end AISafetyAtlas.Causal
