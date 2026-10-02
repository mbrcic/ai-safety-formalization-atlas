module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Real.Basic

/-!
# Retargetable decision-makers have orbit-level tendencies

Turner and Tadepalli, *Parametrically Retargetable Decision-Makers Tend To Seek
Power*, arXiv:2206.13477v2, section 3. Their section 3 is the whole formal core
of the paper, and it is finite combinatorics on group orbits: no Markov decision
process, no measure, no reward.

## What the section says

A decision-maker is scored by two real functions of a parameter: `fA θ` is how
much it favours outcome set `A` at parameter `θ`, `fB θ` how much it favours `B`.
The parameter lives in a set `Θ` acted on by a group -- print takes the symmetric
group `S_d` permuting `d` states or observations, and the arguments below use only
the group structure, so they are stated for an arbitrary group.

*Retargetable* means: wherever the decision-maker prefers `A`, some permutation of
the parameter flips it to preferring `B`. The results say that this one-directional
flippability forces a **counting** fact about every orbit -- at least `n` times as
many parameters in the orbit favour `B` as favour `A`.

## What this is not

Print's footnote 2 is load-bearing and is repeated here because the module's name
invites the opposite reading: *"We often interpret `A` and `B` as
probability-theoretic events, but no such structure is demanded by our results."*

`A` and `B` are labels. **Nothing in this file is about power.** Theorem 3.6 says
a symmetry in how a decision-maker can be retargeted forces a cardinality
inequality, and that is all it says. The paper's power claim comes from choosing
`B` to be a power-requiring outcome set, which happens in its section 5 and
appendix and rests on the 2021 optimal-policy results over Markov decision
processes. None of that is here, and this module must not be cited as evidence
for a power-seeking tendency.

## Fidelity notes

* Print's section 3 writes one function `f : {A, B} × Θ → ℝ`; two functions
  `fA fB : Ω → ℝ` is the same data and avoids carrying a two-element index.
  **This is print's own rendering, not a choice made here**: the Remark on page
  15, opening appendix B, switches to `f₁(θ) := f(B ∣ θ)` and `f₂(θ) := f(A ∣ θ)`
  *"for compatibility"* with Turner et al. 2021, and says the appendix proofs use
  that notation.
* Print's group is `S_d`. Nothing below uses more than a group acting on the
  parameter type, so the statements are wider than print on that axis. Instantiate
  at `Equiv.Perm (Fin d)` to recover print exactly.
* Finiteness is a hypothesis print does not state, because for `S_d` with `d`
  finite the orbits are automatically finite. `[Finite G]` supplies it here and is
  the same assumption made explicit.
-/

namespace AISafetyAtlas.Sovereignty

universe u v

variable {G : Type u} [Group G] {Ω : Type v} [MulAction G Ω]

/-- **Definition 3.1.** The orbit of `θ` *inside* `Θ`: print's `Orbit|_Θ(θ)`, the
permuted variants of `θ` that `Θ` actually contains. -/
@[expose] public def orbitIn (G : Type u) [Group G] [MulAction G Ω] (Θ : Set Ω)
    (θ : Ω) : Set Ω :=
  MulAction.orbit G θ ∩ Θ

/-- The part of the orbit at which the decision-maker favours `B`. -/
@[expose] public def orbitFavouring (G : Type u) [Group G] [MulAction G Ω]
    (Θ : Set Ω) (fA fB : Ω → ℝ) (θ : Ω) : Set Ω :=
  {θ' ∈ orbitIn G Θ θ | fA θ' < fB θ'}

/-- The part of the orbit at which it favours `A`. Print writes this
`Orbit|_{Θ,A>B}(θ)`. -/
@[expose] public def orbitAgainst (G : Type u) [Group G] [MulAction G Ω]
    (Θ : Set Ω) (fA fB : Ω → ℝ) (θ : Ω) : Set Ω :=
  {θ' ∈ orbitIn G Θ θ | fB θ' < fA θ'}

/--
**Definition 3.2.** `fB` beats `fA` for most orbit elements, by a factor of `n`:
in every orbit, at least `n` times as many parameters favour `B` as favour `A`.

Print writes this `f(B | θ) ≥^n_{most: Θ} f(A | θ)`.
-/
@[expose] public def MostOrbit (G : Type u) [Group G] [MulAction G Ω] (n : ℕ)
    (Θ : Set Ω) (fA fB : Ω → ℝ) : Prop :=
  ∀ θ ∈ Θ, n * (orbitAgainst G Θ fA fB θ).ncard ≤ (orbitFavouring G Θ fA fB θ).ncard

/--
**Definition 3.5.** `fA`, `fB` are `n`-retargetable on `Θ`: at every parameter
there are `n` group elements which each turn a preference for `A` into a
preference for `B`, stay inside `Θ`, and send distinct parameters to distinct
places.

The three clauses are print's, in print's order.
-/
@[expose] public def MultiplyRetargetable (G : Type u) [Group G] [MulAction G Ω]
    (n : ℕ) (Θ : Set Ω) (fA fB : Ω → ℝ) : Prop :=
  ∀ θ ∈ Θ, ∃ φ : Fin n → G,
    (∀ i, ∀ θA ∈ orbitAgainst G Θ fA fB θ, fA (φ i • θA) < fB (φ i • θA)) ∧
    (∀ i, ∀ θA ∈ orbitAgainst G Θ fA fB θ, φ i • θA ∈ Θ) ∧
    (∀ i j, i ≠ j → ∀ θA ∈ orbitAgainst G Θ fA fB θ,
      ∀ θ' ∈ orbitAgainst G Θ fA fB θ, φ i • θA ≠ φ j • θ')

/--
**Definition 3.3.** Simple retargetability: a *single* group element flips every
`A`-preference in `Θ` to a `B`-preference.
-/
@[expose] public def SimplyRetargetable (G : Type u) [Group G] [MulAction G Ω]
    (Θ : Set Ω) (fA fB : Ω → ℝ) : Prop :=
  ∃ φ : G, ∀ θA ∈ Θ, fB θA < fA θA → fA (φ • θA) < fB (φ • θA)

/-! ## The counting argument -/

/-- An orbit inside `Θ` is finite when the group is. Print does not state this
because it works with `S_d`. -/
public theorem orbitIn_finite [Finite G] (Θ : Set Ω) (θ : Ω) :
    (orbitIn G Θ θ).Finite :=
  (Set.finite_range fun g : G => g • θ).subset fun _ hx => hx.1

/--
**Theorem 3.6.** An `n`-retargetable pair has orbit-level tendencies.

The proof is print's: each `φ i` carries the `A`-favouring part of the orbit into
the `B`-favouring part, injectively because the action is; the `n` images are
pairwise disjoint by the third clause; so the `B`-favouring part contains `n`
disjoint copies of the `A`-favouring one.
-/
public theorem MultiplyRetargetable.mostOrbit [Finite G] {n : ℕ} {Θ : Set Ω}
    {fA fB : Ω → ℝ} (h : MultiplyRetargetable G n Θ fA fB) :
    MostOrbit G n Θ fA fB := by
  intro θ hθ
  obtain ⟨φ, hflip, hmem, hdisj⟩ := h θ hθ
  classical
  set S := orbitAgainst G Θ fA fB θ with hS
  set T := orbitFavouring G Θ fA fB θ with hT
  have hTfin : T.Finite := (orbitIn_finite Θ θ).subset fun _ hx => hx.1
  -- the injection `Fin n × S → T`
  have hmaps : ∀ (i : Fin n) (x : Ω), x ∈ S → φ i • x ∈ T := by
    intro i x hx
    refine ⟨⟨?_, hmem i x hx⟩, hflip i x hx⟩
    obtain ⟨⟨⟨g, hg⟩, _⟩, _⟩ := hx
    refine ⟨φ i * g, ?_⟩
    show (φ i * g) • θ = φ i • x
    rw [mul_smul]
    exact congrArg (φ i • ·) hg
  have key : n * S.ncard ≤ T.ncard := by
    have hinj : Function.Injective
        (fun p : Fin n × S => (⟨φ p.1 • (p.2 : Ω), hmaps p.1 _ p.2.2⟩ : T)) := by
      rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ hEq
      have hxy : φ i • (x : Ω) = φ j • (y : Ω) := congrArg Subtype.val hEq
      have hij : i = j := by
        by_contra hne
        exact hdisj i j hne x hx y hy hxy
      subst hij
      have : (x : Ω) = y := MulAction.injective (φ i) hxy
      simp [this]
    have hfin : Finite T := hTfin
    have := Nat.card_le_card_of_injective _ hinj
    simpa [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using this
  exact key

/--
**Proposition 3.4.** Simple retargetability gives the `n = 1` case.

Print's footnote 3 records that definition 3.3 implicitly assumes `Θ` is closed
under the action; that assumption is explicit here as `hclosed`, since without it
the retargeted parameter need not lie in `Θ` and clause 2 of definition 3.5 fails.
-/
public theorem SimplyRetargetable.mostOrbit [Finite G] {Θ : Set Ω} {fA fB : Ω → ℝ}
    (hclosed : ∀ (g : G), ∀ θ ∈ Θ, g • θ ∈ Θ)
    (h : SimplyRetargetable G Θ fA fB) :
    MostOrbit G 1 Θ fA fB := by
  obtain ⟨φ, hφ⟩ := h
  refine MultiplyRetargetable.mostOrbit (fun θ _ => ⟨fun _ => φ, ?_, ?_, ?_⟩)
  · intro _ θA hθA; exact hφ θA hθA.1.2 hθA.2
  · intro _ θA hθA; exact hclosed φ θA hθA.1.2
  · intro i j hij; exact absurd (Subsingleton.elim i j) hij

/-! ## What "more options" means, and what it would take to reach power

Section 3 above is deliberately not about power. This section adds the paper's
formal sense of one option set being *larger* than another -- which is where the
power reading enters -- and records exactly what still stands between that notion
and the paper's power theorem.
-/

/--
**Definition A.6.** One set is *similar* to another when some group element
carries it across.
-/
@[expose] public def SimilarUnder (G : Type u) [Group G] [MulAction G Ω]
    (X Y : Set Ω) : Prop :=
  ∃ φ : G, (fun ω => φ • ω) '' X = Y

/--
**Definition A.7, containment of set copies.** `B` contains `n` copies of `A`
when there are `n` group elements carrying `A` into `B` whose images are fixed by
each other.

This is the paper's formal sense of *`B` offers at least `n` times as many
options as `A`*, and it is the notion that carries the power reading: the
power-seeking claim is that a set which contains several copies of another gets
chosen more often. Print takes the `φ i` to be involutions of the symmetric
group; nothing below needs that, so it is not required here.

The third clause -- each `φ i` fixes every *other* image -- is what stops the
copies from collapsing onto one another, and it is what the counting argument
consumes.
-/
@[expose] public def ContainsCopies (G : Type u) [Group G] [MulAction G Ω]
    (n : ℕ) (B A : Set Ω) : Prop :=
  ∃ φ : Fin n → G,
    (∀ i, (fun ω => φ i • ω) '' A ⊆ B) ∧
    (∀ i j, i ≠ j → (fun ω => φ i • ω) '' ((fun ω => φ j • ω) '' A)
      = (fun ω => φ j • ω) '' A)

/-- **A superset contains one copy of what it contains.** The identity carries
`A` into `B`, and the third clause is vacuous at `n = 1`, so containment of one
copy is weaker than inclusion and implied by it. -/
public theorem containsCopies_one_of_subset {A B : Set Ω} (h : A ⊆ B) :
    ContainsCopies G 1 B A := by
  refine ⟨fun _ => 1, fun _ => ?_, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  simpa using h

/-- Containment of `n` copies weakens to containment of fewer. -/
public theorem ContainsCopies.mono {n m : ℕ} {A B : Set Ω} (hmn : m ≤ n)
    (h : ContainsCopies G n B A) : ContainsCopies G m B A := by
  obtain ⟨φ, hsub, hfix⟩ := h
  refine ⟨fun i => φ ⟨i, lt_of_lt_of_le i.2 hmn⟩, fun i => hsub _, fun i j hij => ?_⟩
  refine hfix _ _ fun hEq => hij ?_
  simp only [Fin.mk.injEq] at hEq
  exact Fin.val_injective hEq

/-! ### From here to power: what is proved, and what is not

The paper's bridge from section 3 to a power claim is **Theorem A.13**: for an
*EU-determined* decision-making function, if `B` contains `n` copies of `A` via
permutations that also fix the choice set `C`, then `B` is chosen at `n` times as
many orbit parameters as `A`.

**That theorem is now proved**, in `AISafetyAtlas.Sovereignty.EUDetermined`, along
with the whole appendix-B chain print routes it through: lemma B.7, definition
B.8, lemma B.9, lemma B.10, definition A.12 and lemma B.11.
`AISafetyAtlas.Examples.Sovereignty.EUDetermined` inhabits its hypotheses and
shows the counting conclusion is not about an empty set.

It does not reduce to `MultiplyRetargetable.mostOrbit` above; B.9 supplies B.7's
four conditions, and B.7 rebuilds definition 3.5 from them.

**Two things `ContainsCopies` above gets wrong for that chain, and where they are
fixed.** Print's definition A.7 requires the `φ i` to be **involutions**, and
`ContainsCopies` drops that, which is sound for its own two consumers but not for
B.7 -- print's equations (24), (31) and (36) each rewrite `φ i ⁻¹` to `φ i`.
`InvolutiveCopies` is definition A.7 verbatim, and
`InvolutiveCopies.containsCopies` records that it is the stronger reading.

**What still stands between A.13 and a claim about power.** A.13 says an
EU-determined selector prefers the option set containing more *copies* of the
other. Nothing in it mentions states, actions, time, or reward; `A`, `B` and `C`
are finite sets of vectors. The word *power* enters only in the paper's
**appendix D**, which instantiates them as sets of recurrent state distributions
in a Markov decision process, so that "more copies" becomes "more environmental
cycles reachable". That instantiation is **not** carried out here, and its
inventory is:

* **Definition D.6**, rewardless MDP: a finite state and action space with a
  transition from state-action pairs to distributions over states. The stochastic
  corrupt-reward development on the wireheading branch already carries exactly
  this object, and wider, since it demands no finiteness; that branch is not
  merged here, which is why no declaration is named.
* **Definition D.8**, stationary deterministic policies and the discounted state
  visit distribution, the sum over time of the discounted expected basis vector of
  the state reached. The policies in that same wireheading development read the
  whole observed history rather than the current state, and its runs are
  finite-horizon and undiscounted, so the visit distribution is absent.
* **Definition D.9**, recurrent state distributions: the Abel limit as the
  discount tends to one. Absent, and its existence is a theorem of Puterman's
  that the pinned Mathlib does not carry.
* **Definitions D.10 and D.11**, average-optimal policies and the power theorem
  itself. Absent.

So one of the four ingredients exists and it is the cheapest. Until the rest do,
**neither this module nor `EUDetermined` licenses a claim about power** -- what
they license is a claim about option-set size under retargeting.
-/

end AISafetyAtlas.Sovereignty
