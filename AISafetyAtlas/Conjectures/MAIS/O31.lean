module

public import AISafetyAtlas.Conjectures.BinaryPair
public import AISafetyAtlas.Causal.Decision
public import AISafetyAtlas.Causal.EffectiveGenericity
public import AISafetyAtlas.Causal.ParameterChart
public import AISafetyAtlas.Causal.Query
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import AISafetyAtlas.Conjectures.MAIS.O31Chart

/-!
# MAIS-O31 — the chain classification candidate

`q:chain` asks which table parameters are `Σ_W`-identifiable. No truth-valued
proposition is that question, so this transcribes the candidate answer submitted
in MAIS issue #8.

Stated at the MAIS revision pinned in `docs/provenance/mais-source-pin.md`.
Defining a proposition asserts nothing about its truth; resolutions live in
`AISafetyAtlas/Examples/Conjectures/`.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.BinaryPair

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
variable {dim : C → ℕ}

/-- The exclusions MAIS issue #8's own Scope section names: "endpoint ties, CPT
boundaries, and exact margin boundaries are excluded".

Endpoint ties are excluded by the chamber disjunct in the statement. This is the
other two: every table entry is *strictly* inside `[λ, 1-λ]` and every edge
strength is *strictly* above `λ`. It is a strengthening of `Valid`, not a
replacement — the comparison class the identifiability quantifier ranges over
stays `𝕄(sk, λ)` with its closed margins, as `q:chain` specifies. -/
@[expose] public def O31ChainModel.Generic {n : ℕ} (lam : ℝ) (M : O31ChainModel n) : Prop :=
  lam < M.root ∧ M.root < 1 - lam ∧
    (∀ i x, lam < M.transition i x ∧ M.transition i x < 1 - lam) ∧
    ∀ i, lam < |M.transition i 1 - M.transition i 0|

/-- The literal table coordinates named by MAIS-O31. -/
public inductive O31Coordinate (n : ℕ) where
  | root
  | transition (child : Fin n) (parentValue : Fin 2)
  deriving DecidableEq, Fintype

/-- Read one literal root or transition-table coordinate. -/
@[expose] public def O31ChainModel.coordinate {n : ℕ} (M : O31ChainModel n) :
    O31Coordinate n → ℝ
  | .root => M.root
  | .transition child parentValue => M.transition child parentValue

/-- Pointwise identifiability of one literal coordinate from the restricted behavior. -/
@[expose] public noncomputable def O31IdentifiesCoordinate {n : ℕ} (lam t : ℝ)
    (j : Fin (n + 1)) (M : O31ChainModel n) (coordinate : O31Coordinate n) : Prop :=
  ∀ M' : O31ChainModel n, M'.Valid lam → O31BehaviorEqAt t j M M' →
    M'.coordinate coordinate = M.coordinate coordinate

/-- The downstream transfer from a hard-fixed `C_j` straddles the decision threshold. -/
@[expose] public noncomputable def O31StraddlingChamber {n : ℕ} (t : ℝ)
    (j : Fin (n + 1)) (M : O31ChainModel n) : Prop :=
  let p₀ := M.targetProbability (o31SingleNodeProfile j (fun _ ↦ 0))
  let p₁ := M.targetProbability (o31SingleNodeProfile j (fun _ ↦ 1))
  (p₀ - t) * (p₁ - t) < 0

/-- The two transfer endpoints lie strictly on the same side of the threshold.

Exposed to match `O31StraddlingChamber`. The candidate's antecedent is the disjunction of the two, so exposing only one branch would let a consumer reason about half of it. -/
@[expose] public noncomputable def O31SameSideChamber {n : ℕ} (t : ℝ)
    (j : Fin (n + 1)) (M : O31ChainModel n) : Prop :=
  let p₀ := M.targetProbability (o31SingleNodeProfile j (fun _ ↦ 0))
  let p₁ := M.targetProbability (o31SingleNodeProfile j (fun _ ↦ 1))
  0 < (p₀ - t) * (p₁ - t)

/-- The literal-coordinate classification submitted in MAIS issue #8. -/
@[expose] public def O31CoordinateCandidate {n : ℕ} (j : Fin (n + 1)) :
    O31Coordinate n → Prop
  | .root => j = Fin.last n
  | .transition _ _ => False

/-- The observational mass `r = P(C_j = 1)` that MAIS issue #8's first bullet
claims behavior identifies in the straddling chamber. It is not a literal table
coordinate, which is why it needs its own reading. -/
@[expose] public noncomputable def O31ChainModel.nodeMass {n : ℕ} (M : O31ChainModel n)
    (j : Fin (n + 1)) : ℝ :=
  ∑ v : Fin (n + 1) → Fin 2, if v j = 1 then M.jointProb (fun _ ↦ id) v else 0

/-- Pointwise identifiability of `r` from the restricted behavior. -/
@[expose] public noncomputable def O31IdentifiesNodeMass {n : ℕ} (lam t : ℝ)
    (j : Fin (n + 1)) (M : O31ChainModel n) : Prop :=
  ∀ M' : O31ChainModel n, M'.Valid lam → O31BehaviorEqAt t j M M' →
    M'.nodeMass j = M.nodeMass j

/-! ## The identification predicates, at print's own comparison class

`q:chain` fixes the comparison class in its own parentheses: *"comparison class:
the models of `𝕄(sk, λ)` carrying this chain graph, so that all the parameters
are defined"*. Issue #8 answers that question and does not redefine the class,
so its claim is about the printed one.

The two predicates above quantify over `O31ChainModel n` — chart points. That is
the direction that gets **easier** in a smaller class: ruling out a collision is
easier when there are fewer models to collide with, so identification proved over
chart points alone would assert less than print. Until 2026-08-23 nothing closed
the gap, and `O31Chart.lean`'s header said so.

`exists_O31ChainModel_toModel_eq` closes it, and the two theorems below are what
walking across the bridge looks like: each predicate is *equivalent* to its own
statement against every model of `𝕄(sk, λ)` carrying the chain graph. Building
the bridge and not crossing it would have left the conjecture stated over the
smaller class with a lemma nearby that nothing used. -/

/-- **Coordinate identification is print's, not the chart's.** -/
public theorem o31IdentifiesCoordinate_iff_class {n : ℕ} {lam g₀ g₁ t : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) {j : Fin (n + 1)} {M : O31ChainModel n}
    (hM : M.Valid lam) (coordinate : O31Coordinate n) :
    O31IdentifiesCoordinate lam t j M coordinate ↔
      ∀ (N : Model (Fin (n + 1)) (binaryDim (Fin (n + 1))) ℝ)
        (hclass : (o31Skeleton (n := n) hg).MarginClass N lam)
        (hpar : N.parents = o31ChainParents),
        O31KernelBehaviorEqAt t j M (O31ChainModel.ofModel N)
            (M.inUnitBox_of_valid hM)
            (O31ChainModel.inUnitBox_of_valid
              (O31ChainModel.ofModel_valid hg hclass hpar)) →
          (O31ChainModel.ofModel N).coordinate coordinate
            = M.coordinate coordinate := by
  constructor
  · intro hid N hclass hpar hbeh
    exact hid _ (O31ChainModel.ofModel_valid hg hclass hpar)
      ((o31BehaviorEqAt_iff_kernel _ _ _ _ _ _).2 hbeh)
  · intro hcl M' hM' hbeh
    have hpar : (M'.toModel (M'.inUnitBox_of_valid hM')).parents = o31ChainParents := rfl
    have hback : O31ChainModel.ofModel (M'.toModel (M'.inUnitBox_of_valid hM')) = M' :=
      M'.ofModel_toModel _
    have hbeh' : O31BehaviorEqAt t j M
        (O31ChainModel.ofModel (M'.toModel (M'.inUnitBox_of_valid hM'))) := by
      rw [hback]; exact hbeh
    have := hcl (M'.toModel (M'.inUnitBox_of_valid hM'))
      (M'.toModel_marginClass hg hM') hpar
      ((o31BehaviorEqAt_iff_kernel _ _ _ _ _ _).1 hbeh')
    rwa [hback] at this

/-- **Node-mass identification is print's, not the chart's.** -/
public theorem o31IdentifiesNodeMass_iff_class {n : ℕ} {lam g₀ g₁ t : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) {j : Fin (n + 1)} {M : O31ChainModel n}
    (hM : M.Valid lam) :
    O31IdentifiesNodeMass lam t j M ↔
      ∀ (N : Model (Fin (n + 1)) (binaryDim (Fin (n + 1))) ℝ)
        (hclass : (o31Skeleton (n := n) hg).MarginClass N lam)
        (hpar : N.parents = o31ChainParents),
        O31KernelBehaviorEqAt t j M (O31ChainModel.ofModel N)
            (M.inUnitBox_of_valid hM)
            (O31ChainModel.inUnitBox_of_valid
              (O31ChainModel.ofModel_valid hg hclass hpar)) →
          (O31ChainModel.ofModel N).nodeMass j = M.nodeMass j := by
  constructor
  · intro hid N hclass hpar hbeh
    exact hid _ (O31ChainModel.ofModel_valid hg hclass hpar)
      ((o31BehaviorEqAt_iff_kernel _ _ _ _ _ _).2 hbeh)
  · intro hcl M' hM' hbeh
    have hpar : (M'.toModel (M'.inUnitBox_of_valid hM')).parents = o31ChainParents := rfl
    have hback : O31ChainModel.ofModel (M'.toModel (M'.inUnitBox_of_valid hM')) = M' :=
      M'.ofModel_toModel _
    have hbeh' : O31BehaviorEqAt t j M
        (O31ChainModel.ofModel (M'.toModel (M'.inUnitBox_of_valid hM'))) := by
      rw [hback]; exact hbeh
    have := hcl (M'.toModel (M'.inUnitBox_of_valid hM'))
      (M'.toModel_marginClass hg hM') hpar
      ((o31BehaviorEqAt_iff_kernel _ _ _ _ _ _).1 hbeh')
    rwa [hback] at this

/--
**MAIS-O31, candidate complete statement.**

The whole claim of MAIS issue #8, at its own quantifiers. In the straddling
chamber behavior identifies `r = P(C_j = 1)`; and a literal table coordinate is
identified exactly when the transfer straddles the threshold, the intervened
variable is the root, and the coordinate is the root probability — so in the
same-side chamber none is. Defining this proposition does not assert or review
the pending submission.

Two things are read from the source rather than supplied:

* **The exclusions, verbatim.** Issue #8's Scope section excludes "endpoint
  ties, CPT boundaries, and exact margin boundaries". The chamber disjunct
  excludes the first; `O31ChainModel.Generic` excludes the other two. The
  comparison class inside `O31IdentifiesCoordinate` keeps `q:chain`'s own
  closed-margin `𝕄(sk, λ)`.
* **Both bullets.** The `r` clause is stated as the implication the issue
  asserts, not as an equivalence it does not.

Two restrictions that were the atlas's own have been withdrawn, and the
statement is now at the issue's quantifier on both.

* **Every threshold.** An earlier statement quantified over an
  `O31UtilityGap` and derived `t`, restricting the issue's free `t ∈ (0,1)` to
  thresholds induced by margin-admissible utilities. This statement quantifies
  over `t` directly and carries no utility-gap hypothesis.
* **Any chain length.** The statement required `0 < n`, so chains of one node
  were excluded. `q:chain` counts `2(m-1)+1` table parameters and rules out no
  `m`; at `m = 1` that is the single root probability, and (M4)'s edge condition
  is vacuous rather than violated. Nothing in the source or in issue #8 excludes
  it, so neither does this.

**Non-vacuity is checked.** Inhabiting the pieces separately leaves the
**chamber disjunct** — the clause that makes the antecedent a statement about a
model's position relative to the threshold — without a witness, and nothing then
rules out hypotheses no model meets. `o31_antecedent_inhabited`
closes that on a two-node chain at margin `1/10`: root `2/5`, transitions `1/5`
and `7/10`, threshold `1/2`. It lands on the *straddling*
branch, which is the branch issue #8's `r` bullet is about, so that implication's
hypothesis is inhabited too.
-/
@[expose] public noncomputable def maisO31_chainClassificationCandidate : Prop :=
  ∀ (n : ℕ) (lam t : ℝ) (j : Fin (n + 1)) (M : O31ChainModel n),
    0 < t → t < 1 → M.Valid lam → M.Generic lam →
      (O31StraddlingChamber t j M ∨ O31SameSideChamber t j M) →
      (O31StraddlingChamber t j M → O31IdentifiesNodeMass lam t j M) ∧
        ∀ coordinate : O31Coordinate n,
          O31IdentifiesCoordinate lam t j M coordinate ↔
            O31StraddlingChamber t j M ∧ O31CoordinateCandidate j coordinate

/-- **The chart-quantified conjecture covers every printed model**, so its outer
binder is not a narrowing either.

`o31IdentifiesCoordinate_iff_class` and `o31IdentifiesNodeMass_iff_class` fix the
*inner* quantifier — the rivals `M'` a coordinate has to be identified against.
The conjecture's *outer* binder is a second and separate exposure:
`maisO31_chainClassificationCandidate` reads `∀ M : O31ChainModel n`, so on its
face it classifies chart points, and a universal over a smaller class asserts
*less*. Proving the chart onto makes the two ranges coincide; it does not by
itself state that they do, and a surjectivity lemma with no consumer leaves the
weaker reading standing.

This is that consumer. Given the conjecture, every model of `𝕄(sk, λ)` carrying
the printed chain graph gets the classification, read at the chart point its own
tables name. The proof is an application — the content is entirely in
`O31ChainModel.ofModel_valid`, which is what says a printed model *has* such a
chart point. -/
public theorem o31Classification_of_candidate {n : ℕ} {lam g₀ g₁ t : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) (h : maisO31_chainClassificationCandidate)
    {j : Fin (n + 1)} {N : Model (Fin (n + 1)) (binaryDim (Fin (n + 1))) ℝ}
    (hclass : (o31Skeleton (n := n) hg).MarginClass N lam)
    (hpar : N.parents = o31ChainParents)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hgen : (O31ChainModel.ofModel N).Generic lam)
    (hcham : O31StraddlingChamber t j (O31ChainModel.ofModel N) ∨
      O31SameSideChamber t j (O31ChainModel.ofModel N)) :
    (O31StraddlingChamber t j (O31ChainModel.ofModel N) →
        O31IdentifiesNodeMass lam t j (O31ChainModel.ofModel N)) ∧
      ∀ coordinate : O31Coordinate n,
        O31IdentifiesCoordinate lam t j (O31ChainModel.ofModel N) coordinate ↔
          O31StraddlingChamber t j (O31ChainModel.ofModel N) ∧
            O31CoordinateCandidate j coordinate :=
  h n lam t j (O31ChainModel.ofModel N) ht0 ht1
    (O31ChainModel.ofModel_valid hg hclass hpar) hgen hcham

private noncomputable def o31StatementWitnessModel : O31ChainModel 1 where
  root := 2 / 5
  transition := fun _ x ↦ if x = 0 then 1 / 5 else 7 / 10

private example : o31StatementWitnessModel.Valid (1 / 10) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · norm_num [InMarginInterval, o31StatementWitnessModel]
  · intro i x
    fin_cases i
    fin_cases x <;> norm_num [InMarginInterval, o31StatementWitnessModel]
  · intro i
    fin_cases i
    norm_num [o31StatementWitnessModel]

private example : o31StatementWitnessModel.Generic (1 / 10) := by
  refine ⟨by norm_num [o31StatementWitnessModel], by
    norm_num [o31StatementWitnessModel], ?_, ?_⟩
  · intro i x
    fin_cases i
    fin_cases x <;> norm_num [o31StatementWitnessModel]
  · intro i
    fin_cases i
    norm_num [o31StatementWitnessModel]

private example : O31UtilityGap (1 / 10) (-1 / 2) (1 / 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show |(-1 / 2 : ℝ)| = 1 / 2 by rw [abs_of_neg] <;> norm_num]
    norm_num
  · rw [show |(1 / 2 : ℝ)| = 1 / 2 by rw [abs_of_pos]; norm_num]
    norm_num

/-- The other sign order (M3) permits, which the previous statement excluded.
Print's `g(z⁺) > 0 > g(z⁻)` is existential over the slice and does not say which
of `g(0)`, `g(1)` is the positive one, so both orders must inhabit the gap. -/
private example : O31UtilityGap (1 / 10) (1 / 2) (-1 / 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show |(1 / 2 : ℝ)| = 1 / 2 by rw [abs_of_pos]; norm_num]
    norm_num
  · rw [show |(-1 / 2 : ℝ)| = 1 / 2 by rw [abs_of_neg] <;> norm_num]
    norm_num

/-- The threshold under the reversed order lands in `(0, 1)` as well, and at the
mirrored point: `g₀ = 1/2, g₁ = -1/2` gives `1/2` too, by symmetry of that
witness. -/
private example : o31Threshold (1 / 2) (-1 / 2) = 1 / 2 := by
  norm_num [o31Threshold]

private example : o31Threshold (-1 / 2) (1 / 2) = 1 / 2 := by
  norm_num [o31Threshold]

/-! ## `q:chain` as a find-all specification

`q:chain` asks *"which of the `2(m-1)+1` table parameters are
`Σ_W`-identifiable for almost every `θ`"*. That is an instruction, and no `Prop`
is `Same` as it — but *"this is the set"* is a proposition, and it is the one an
answer would have to prove. `maisO31_chainClassificationCandidate` is **not**
this: it grades the classification submitted in MAIS issue #8, which answers to
that artifact rather than to the printed question. -/

/-- **A candidate answer set is correct when its membership agrees with
identifiability at every one of the `2(m-1)+1` coordinates.**

Soundness and completeness together — an inclusion in one direction would leave
the interesting half open, and print asks *which* parameters, not *some*.

The predicate is stated at a chart point; `o31IdentifiesCoordinate_iff_class`
carries each membership to `q:chain`'s own comparison class, which is the
direction an identification claim needs, since ruling out a rival gets easier
when there are fewer rivals. -/
public noncomputable def IsO31IdentifiableSet {n : ℕ} (lam t : ℝ) (j : Fin (n + 1))
    (M : O31ChainModel n) (S : Set (O31Coordinate n)) : Prop :=
  ∀ c : O31Coordinate n, c ∈ S ↔ O31IdentifiesCoordinate lam t j M c

public theorem isO31IdentifiableSet_iff {n : ℕ} (lam t : ℝ) (j : Fin (n + 1))
    (M : O31ChainModel n) (S : Set (O31Coordinate n)) :
    IsO31IdentifiableSet lam t j M S ↔
      ∀ c : O31Coordinate n, c ∈ S ↔ O31IdentifiesCoordinate lam t j M c := Iff.rfl

/-! ### The chain's parameter space, and `q:chain`'s *almost every θ*

`q:chain` asks for the identifiable set *"for almost every `θ`"*, so the answer
is **one** set of coordinates and a null family of parameters is forgiven. That
needs a measure on the parameters, and the chart is already a real coordinate
tuple: `O31ChainModel n` is a root probability and `2n` transition entries, so
its parameter space is `ℝ × (Fin n → Fin 2 → ℝ)` and Lebesgue measure on that
product is Mathlib's, with no construction of the atlas's own.

Until 2026-08-24 the atlas had Lebesgue measure on the two-node chain's `ℝ³`
only, reached by writing three coordinates out by hand in
`Examples/Conjectures/MAIS/O31Measure.lean`, and the printed question was
recorded as unstatable for that reason. -/

/-- The chain's parameter tuple: a root probability and `2n` transition entries.
This is `θ`, and it carries Lebesgue measure because it is a finite product of
copies of `ℝ`. -/
public abbrev O31ChainCoords (n : ℕ) := ℝ × (Fin n → Fin 2 → ℝ)

/-- Read a chain model off its parameters. -/
@[expose] public def O31ChainModel.ofCoords {n : ℕ} (p : O31ChainCoords n) :
    O31ChainModel n where
  root := p.1
  transition := p.2

/-- Read the parameters off a chain model. -/
@[expose] public def O31ChainModel.toCoords {n : ℕ} (M : O31ChainModel n) :
    O31ChainCoords n := (M.root, M.transition)

@[simp] public theorem O31ChainModel.ofCoords_toCoords {n : ℕ} (M : O31ChainModel n) :
    O31ChainModel.ofCoords M.toCoords = M := rfl

@[simp] public theorem O31ChainModel.toCoords_ofCoords {n : ℕ} (p : O31ChainCoords n) :
    (O31ChainModel.ofCoords p).toCoords = p := rfl

/-- The chart and its parameter space are the same objects counted twice, which
is what makes an *almost every `θ`* statement about parameters a statement about
models. -/
public theorem O31ChainModel.ofCoords_surjective {n : ℕ} :
    Function.Surjective (O31ChainModel.ofCoords (n := n)) :=
  fun M ↦ ⟨M.toCoords, rfl⟩

/-- **`q:chain` at its own quantifier**: one answer set, correct at almost every
parameter of the printed comparison class.

This is print's question rather than a pointwise instance of it. The answer set
`S` is quantified **outside** the parameter, so it cannot vary with the model —
which is exactly what the pointwise form allows and why the pointwise form has a
circular answer and this one does not: `{c | O31IdentifiesCoordinate lam t j M c}`
mentions `M` and is therefore not a candidate here at all.

The margin condition sits inside the almost-everywhere quantifier as a
hypothesis, because print's comparison class is *"the models of `𝕄(sk, λ)`
carrying this chain graph"* and a parameter outside it is not being asked about.
A null exceptional family is forgiven, and unlike
`IsO31IdentifiableSetOffExceptional` below, *null* is what the statement says
rather than something a candidate supplies. -/
public noncomputable def IsO31IdentifiableSetAlmostEverywhere {n : ℕ} (lam t : ℝ)
    (j : Fin (n + 1)) (S : Set (O31Coordinate n)) : Prop :=
  ∀ᵐ p : O31ChainCoords n,
    (O31ChainModel.ofCoords p).Valid lam →
      IsO31IdentifiableSet lam t j (O31ChainModel.ofCoords p) S

public theorem isO31IdentifiableSetAlmostEverywhere_iff {n : ℕ} (lam t : ℝ)
    (j : Fin (n + 1)) (S : Set (O31Coordinate n)) :
    IsO31IdentifiableSetAlmostEverywhere lam t j S ↔
      ∀ᵐ p : O31ChainCoords n,
        (O31ChainModel.ofCoords p).Valid lam →
          IsO31IdentifiableSet lam t j (O31ChainModel.ofCoords p) S := Iff.rfl

/-! ### A finite carrier for an answer, not an admissibility condition

`IsO31IdentifiableSetAlmostEverywhere` takes a `Set (O31Coordinate n)`, which in
Lean is a predicate, and a predicate may be *defined* by the condition it is
supposed to characterize. That is the gap `isO31IdentifiableSet_self` below
exhibits for the pointwise form, and the almost-everywhere form does not escape
it by binding `S` outside the quantifier: the set of coordinates identifiable at
almost every parameter is itself a set, and handing it back answers nothing.

`O31Coordinate n` is **finite**, with `2n + 1` inhabitants — one root cell and
one per (child, parent value) pair, exactly the count `q:chain` writes. A
`Finset` is therefore a convenient presentation of a proposed list, but it does
not close the circularity gap. Classical filtering converts any predicate on a
finite type to a `Finset`, including a predicate defined by the property being
classified. `isO31IdentifiableAnswer_of_set` below proves the consequence: any
correct `Set` answer automatically yields the `Finset` form.

The ledger therefore records O31 admissibility as `Unformalized`. Excluding a
restatement would require a source-backed answer grammar, such as an explicit
combinatorial expression; `q:chain` names none. -/

/-- **`q:chain`'s answer with a finite carrier.** This is a convenient list
format, not an admissibility condition: `isO31IdentifiableAnswer_of_set` shows
that classical filtering can turn any correct set predicate into this form. -/
public noncomputable def IsO31IdentifiableAnswer {n : ℕ} (lam t : ℝ)
    (j : Fin (n + 1)) (F : Finset (O31Coordinate n)) : Prop :=
  IsO31IdentifiableSetAlmostEverywhere lam t j (F : Set (O31Coordinate n))

public theorem isO31IdentifiableAnswer_iff {n : ℕ} (lam t : ℝ) (j : Fin (n + 1))
    (F : Finset (O31Coordinate n)) :
    IsO31IdentifiableAnswer lam t j F ↔
      IsO31IdentifiableSetAlmostEverywhere lam t j (F : Set (O31Coordinate n)) :=
  Iff.rfl

/-- Every predicate on the finite coordinate type can be presented as a
`Finset`, including a predicate that merely restates the classification. -/
public noncomputable def o31FinsetOfSet {n : ℕ} (S : Set (O31Coordinate n)) :
    Finset (O31Coordinate n) := by
  classical
  exact Finset.univ.filter fun c ↦ c ∈ S

/-- Classical filtering preserves the supplied coordinate predicate exactly. -/
public theorem coe_o31FinsetOfSet {n : ℕ} (S : Set (O31Coordinate n)) :
    (o31FinsetOfSet S : Set (O31Coordinate n)) = S := by
  classical
  ext c
  simp [o31FinsetOfSet]

/-- The `Finset` carrier adds no admissibility: every correct set answer yields
a correct finite-list answer without exposing a classification. -/
public theorem isO31IdentifiableAnswer_of_set {n : ℕ} (lam t : ℝ)
    (j : Fin (n + 1)) (S : Set (O31Coordinate n))
    (hS : IsO31IdentifiableSetAlmostEverywhere lam t j S) :
    IsO31IdentifiableAnswer lam t j (o31FinsetOfSet S) := by
  rw [isO31IdentifiableAnswer_iff]
  simpa only [coe_o31FinsetOfSet] using hS

public instance instDecidableO31CoordinateCandidate {n : ℕ} (j : Fin (n + 1)) :
    DecidablePred (O31CoordinateCandidate (n := n) j) := by
  intro c
  cases c <;> unfold O31CoordinateCandidate <;> infer_instance

/-- The classification submitted in MAIS issue #8, as a list of coordinates. -/
public def o31CandidateFinset {n : ℕ} (j : Fin (n + 1)) :
    Finset (O31Coordinate n) :=
  {c ∈ Finset.univ | O31CoordinateCandidate j c}

/-- The classification submitted in issue #8 has the expected finite-list
presentation. This says nothing about whether that candidate is correct. -/
public theorem coe_o31CandidateFinset {n : ℕ} (j : Fin (n + 1)) :
    (o31CandidateFinset j : Set (O31Coordinate n)) =
      {c : O31Coordinate n | O31CoordinateCandidate j c} := by
  ext c
  simp [o31CandidateFinset]

/-- The answer space is finite and its size is the count `q:chain` writes:
`2(m-1) + 1` table parameters for a chain on `m = n + 1` nodes. -/
public theorem card_o31Coordinate (n : ℕ) :
    Fintype.card (O31Coordinate n) = 2 * n + 1 := by
  have h : Fintype.card (O31Coordinate n)
      = Fintype.card (Unit ⊕ (Fin n × Fin 2)) :=
    Fintype.card_congr
      { toFun := fun c ↦ match c with
          | .root => Sum.inl ()
          | .transition a b => Sum.inr (a, b)
        invFun := fun s ↦ match s with
          | .inl _ => .root
          | .inr (a, b) => .transition a b
        left_inv := by rintro (_ | ⟨a, b⟩) <;> rfl
        right_inv := by rintro (⟨⟩ | ⟨a, b⟩) <;> rfl }
  rw [h]
  simp [Fintype.card_sum, Fintype.card_prod]
  ring

/-- A pointwise answer at every parameter is in particular an answer at almost
every parameter. The converse fails, which is the whole content of the printed
quantifier. -/
public theorem isO31IdentifiableSetAlmostEverywhere_of_forall {n : ℕ} {lam t : ℝ}
    {j : Fin (n + 1)} {S : Set (O31Coordinate n)}
    (h : ∀ M : O31ChainModel n, M.Valid lam → IsO31IdentifiableSet lam t j M S) :
    IsO31IdentifiableSetAlmostEverywhere lam t j S :=
  Filter.Eventually.of_forall fun p ↦ h (O31ChainModel.ofCoords p)

/-- **Print's own shape: one answer set for all but an exceptional family.**

`q:chain` asks for the identifiable set *"for almost every `θ`"*, so the answer
is a single set of coordinates rather than one set per model, and an exceptional
family is forgiven.

**This is not print's question and `IsO31IdentifiableSetAlmostEverywhere` is.**
*Almost every* means the exceptional family is null, and nothing here requires
it to be: a candidate may take `exceptional` to be everything and satisfy this
vacuously. That is a missing piece of the **correctness** condition rather than
an admissibility gap, and no admissibility label repairs it — a specification
print's question does not imply is not the same statement as it.

It is kept because it is the shape a *supplied* exceptional set takes, which is
how a solver would present an answer with its own stated exceptional locus, and
because it is the weaker statement a null-set argument would discharge on the
way to the real one. -/
public noncomputable def IsO31IdentifiableSetOffExceptional {n : ℕ} (lam t : ℝ)
    (j : Fin (n + 1)) (exceptional : Set (O31ChainModel n))
    (S : Set (O31Coordinate n)) : Prop :=
  ∀ M : O31ChainModel n, M.Valid lam → M ∉ exceptional →
    IsO31IdentifiableSet lam t j M S

/-- **The specification admits a circular answer**, exactly as `prob:floor`(c)'s
does: the set defined as *the identifiable coordinates* satisfies it by
unfolding and tells a reader nothing. Stated rather than left implicit, because
no checker surfaces it and the ledger's admissibility field is the only other
place it is recorded. -/
public theorem isO31IdentifiableSet_self {n : ℕ} (lam t : ℝ) (j : Fin (n + 1))
    (M : O31ChainModel n) :
    IsO31IdentifiableSet lam t j M {c | O31IdentifiesCoordinate lam t j M c} :=
  fun _ ↦ Iff.rfl


end AISafetyAtlas.Conjectures.MAIS
